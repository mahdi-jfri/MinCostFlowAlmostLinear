module

public import MinCostFlow.Final.AssemblyDryRunSCDeepCode
public import MinCostFlow.Final.AssemblyDryRunSCSelInitTight
public import MinCostFlow.MinRatio.WireShiftDeepSelect
import MinCostFlow.Final.AssemblyDryRunSCCoreKFBL
import MinCostFlow.MinRatio.WireCoreLenK
import MinCostFlow.MinRatio.WireShiftDeepSpecMonoKFBL
import Mathlib.Tactic

/-!
# Concrete select-aware `shiftDeepChain` block (`AssemblyDryRunSCDeepSelectCode`)

Packages the deterministic select-aware deep-shift wrapper `shiftDeepSelectBody`
(`MinRatio/WireShiftDeepSelectAux.lean`), the inner deep-shift synchronization module
`dryDeepProcs` (`Final/AssemblyDryRunSCDeepCode.lean`), and all select-region refresh helpers
(`selTableWrite`, `dgCopyRefill`, `selectInitInteriorLoop`, `selectFillInteriorLevel`,
`selectFillLastLevel`, `selectRefreshFinalize`, `selCoreLenFill`, `selFilterAbsent`, `selEmbCopy`,
`selectPhiLoop`, `selectRebuildSuffix`, `selectRebuildLevel`, `selectProcessList`,
`selectProcessEdge`, and the four self-contained modules `dgRefillModule`, `selectHeapOpsModule`,
`selectPhiFillModule`, `evalKeyModule`) into a relocatable 88-procedure deterministic
`SolverInnerSubCode` block `dryDeepSelectCode`:

* `dryDeepSelectCodeLen`, `dryDeepSelectProcs`, `dryDeepSelectCode`: the 88-procedure
  deterministic `SolverInnerSubCode` block (`off = 0`).
* `dryDeepSelectCode_hasAll`: extracts every procedure entry and all four sub-module placements
  at `lay.shiftDeepChain` inside `dryLinkedProgramSel`.
* `dryDeepSelectCode_hLastImpl_sel` and `drySC_forestCap_level_sel`: transfers the last-level
  implementation and sparse-core forest-cap contracts into `dryLinkedProgramSel`.
* `dryDeepSelectCode_hDeepInner`: discharges the tight inner `ShiftDeepChainSyncSpecWExtKFBL` at
  `lay.shiftDeepChain + 1` inside `dryLinkedProgramSel` with exact inner bounds `dryDeepSpace`,
  `deepShiftFixedBound`, `deepShiftToolMulBound`, and `wireTreeSyncEditCost + 2`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Concrete 88-procedure deterministic `SolverInnerSubCode` block `dryDeepSelectCode` -/

/-- Fixed length (`88`) of `dryDeepSelectProcs`. -/
def dryDeepSelectCodeLen : ℕ := 88

/-- Concrete relocatable 88-procedure deterministic block placed at `env.innerBase` implementing
`shiftDeepSelectBody` (offset `0`), `dryDeepProcs` (offsets `1 .. 6`), all 16 select-refresh
wrapper procedures (offsets `7 .. 22`), and the four self-contained helper modules
`dgRefillModule` (`23 .. 34`), `selectHeapOpsModule` (`35 .. 56`), `selectPhiFillModule`
(`57 .. 73`), and `evalKeyModule` (`74 .. 87`). -/
def dryDeepSelectProcs (env : SolverInnerEnv) : List Stmt :=
  let b := env.innerBase
  let ops := env.opsBase
  [shiftDeepSelectBody (b + 1) (b + 7) (b + 10) (env.scOp 3) (b + 12) (b + 13)] ++
  (dryDeepProcs { env with innerBase := b + 1 } ++
  ([selTableWriteBody (b + 8),
    selTableRowBody,
    dgCopyRefillBody (b + 34),
    selectInitInteriorLoopBody (b + 10) (b + 11),
    selectFillInteriorLevelBody (env.scOp 2) (env.scOp 4) (b + 9) (b + 14) (b + 16) (b + 17),
    selectFillLastLevelBody (b + 9) (b + 14),
    selectRefreshFinalizeBody (b + 18) (b + 19),
    selCoreLenFillBody (b + 15),
    selCoreLenEdgeBody (ops + 20) (b + 4),
    selFilterAbsentBody,
    selEmbCopyBody (b + 47),
    selectPhiLoopBody (b + 18) (b + 73),
    selectRebuildSuffixBody (b + 19) (b + 20),
    selectRebuildLevelBody (b + 56) (b + 21),
    selectProcessListBody (b + 21) (b + 22),
    selectProcessEdgeBody (b + 74) (b + 53) (b + 55)] ++
  (dgRefillModule (b + 23) ++
  (selectHeapOpsModule (b + 35) 4 ++
  (selectPhiFillModule (b + 57) 4 ++
   evalKeyModule (b + 74) 4)))))

theorem dryDeepSelectProcs_length (env : SolverInnerEnv) :
    (dryDeepSelectProcs env).length = dryDeepSelectCodeLen := by
  unfold dryDeepSelectProcs dryDeepSelectCodeLen
  simp only [List.length_append, List.length_cons, List.length_nil,
    dryDeepProcs_length, dryDeepCodeLen, dgRefillModule_length,
    selectHeapOpsModule_length, selectPhiFillModule_length, evalKeyModule_length]

theorem dryDeepSelectProcs_noRand (env : SolverInnerEnv) :
    ∀ s ∈ dryDeepSelectProcs env, s.NoRand := by
  intro s hs
  unfold dryDeepSelectProcs at hs
  simp only [List.mem_append] at hs
  rcases hs with hEntry | hDeep | hWrap | hDgRef | hHeap | hPhi | hEval
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hEntry
    subst hEntry
    exact shiftDeepSelectBody_noRand ..
  · exact dryDeepProcs_noRand _ s hDeep
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hWrap
    rcases hWrap with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact selTableWriteBody_noRand _
    · exact selTableRowBody_noRand
    · exact dgCopyRefillBody_noRand _
    · exact selectInitInteriorLoopBody_noRand ..
    · exact selectFillInteriorLevelBody_noRand ..
    · exact selectFillLastLevelBody_noRand ..
    · exact selectRefreshFinalizeBody_noRand ..
    · exact selCoreLenFillBody_noRand _
    · exact selCoreLenEdgeBody_noRand ..
    · exact selFilterAbsentBody_noRand
    · exact selEmbCopyBody_noRand _
    · exact selectPhiLoopBody_noRand ..
    · exact selectRebuildSuffixBody_noRand ..
    · exact selectRebuildLevelBody_noRand ..
    · exact selectProcessListBody_noRand ..
    · exact selectProcessEdgeBody_noRand ..
  · exact dgRefillModule_noRand _ s hDgRef
  · exact selectHeapOpsModule_noRand _ _ s hHeap
  · exact selectPhiFillModule_noRand _ _ s hPhi
  · exact evalKeyModule_noRand _ _ s hEval

/-- Relocatable deterministic `SolverInnerSubCode` for select-aware deep shift
(`shiftDeepSelectBody` at offset `0`). -/
def dryDeepSelectCode : SolverInnerSubCode where
  procs := dryDeepSelectProcs
  len := dryDeepSelectCodeLen
  hlen := dryDeepSelectProcs_length
  hnoRand := dryDeepSelectProcs_noRand
  off := 0

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 2. Procedure placement inside `dryLinkedProgramSel` -/

private theorem hasAt_peel_ds {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

/-- Extracts every procedure entry and all four sub-module placements of `dryDeepSelectCode`
at `lay.shiftDeepChain` inside `dryLinkedProgramSel`. -/
theorem dryDeepSelectCode_hasAll (Psc : DrySparseCorePieces)
    (initCode coreCode selectCode termCode selInitCode : SolverInnerSubCode) :
    let inner := dryInnerCodeSel initCode coreCode selectCode termCode dryDeepSelectCode
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    let b := lay.shiftDeepChain
    let ops := mrdsCycleBase
    p.procs[b]? = some (shiftDeepSelectBody (b + 1) (b + 7) (b + 10) (lay.scOp 3)
        (b + 12) (b + 13)) ∧
    p.procs[b + 1]? = some (shiftDeepChainBodyKFBL lay.scInit (lay.scOp 1) (lay.scOp 3)
        (lay.scOp 2) (b + 3) (lay.scOp 5) lay.lastInit (b + 2) (dryPathTreeOp ops 4)
        (dryPathTreeOp ops 1) (dryPathTreeOp ops 0) (b + 5) (b + 6) (ops + 69)) ∧
    p.procs[b + 2]? = some wireSuffixPackEditsBody ∧
    p.procs[b + 3]? = some (wireCoreLenBody (b + 4)) ∧
    p.procs[b + 4]? = some (wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops) ∧
    p.procs[b + 5]? = some pathSlotBindBody ∧
    p.procs[b + 6]? = some (wireCanonCopyBody ops (ops + 4)) ∧
    p.procs[b + 7]? = some (selTableWriteBody (b + 8)) ∧
    p.procs[b + 8]? = some selTableRowBody ∧
    p.procs[b + 9]? = some (dgCopyRefillBody (b + 34)) ∧
    p.procs[b + 10]? = some (selectInitInteriorLoopBody (b + 10) (b + 11)) ∧
    p.procs[b + 11]? = some (selectFillInteriorLevelBody (lay.scOp 2) (lay.scOp 4) (b + 9)
        (b + 14) (b + 16) (b + 17)) ∧
    p.procs[b + 12]? = some (selectFillLastLevelBody (b + 9) (b + 14)) ∧
    p.procs[b + 13]? = some (selectRefreshFinalizeBody (b + 18) (b + 19)) ∧
    p.procs[b + 14]? = some (selCoreLenFillBody (b + 15)) ∧
    p.procs[b + 15]? = some (selCoreLenEdgeBody (ops + 20) (b + 4)) ∧
    p.procs[b + 16]? = some selFilterAbsentBody ∧
    p.procs[b + 17]? = some (selEmbCopyBody (b + 47)) ∧
    p.procs[b + 18]? = some (selectPhiLoopBody (b + 18) (b + 73)) ∧
    p.procs[b + 19]? = some (selectRebuildSuffixBody (b + 19) (b + 20)) ∧
    p.procs[b + 20]? = some (selectRebuildLevelBody (b + 56) (b + 21)) ∧
    p.procs[b + 21]? = some (selectProcessListBody (b + 21) (b + 22)) ∧
    p.procs[b + 22]? = some (selectProcessEdgeBody (b + 74) (b + 53) (b + 55)) ∧
    p.HasAt (b + 23) (dgRefillModule (b + 23)) ∧
    p.HasAt (b + 35) (selectHeapOpsModule (b + 35) 4) ∧
    p.HasAt (b + 57) (selectPhiFillModule (b + 57) 4) ∧
    p.HasAt (b + 74) (evalKeyModule (b + 74) 4) := by
  intro inner p lay b ops
  have hInner := dryLinkedProgramSel_inner_hasAt dryWitnessUsed Psc.sc inner selInitCode
  set env := solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊ lastWordConst
    Psc.sc solverTailBase
  have hInner' : p.HasAt env.innerBase (inner.procs env) := hInner
  unfold inner dryInnerCodeSel at hInner'
  dsimp only at hInner'
  obtain ⟨_, r1⟩ := hasAt_peel_ds (b' := env.innerBase + 1) hInner' (by simp)
  obtain ⟨_, r2⟩ := hasAt_peel_ds (b' := env.innerBase + 1 + initCode.len) r1
    (by simp [initCode.hlen])
  obtain ⟨_, r3⟩ := hasAt_peel_ds (b' := env.innerBase + 1 + initCode.len + coreCode.len) r2
    (by simp [coreCode.hlen])
  obtain ⟨_, r4⟩ := hasAt_peel_ds
    (b' := env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len) r3
    (by simp [selectCode.hlen])
  obtain ⟨_, hAtRaw⟩ := hasAt_peel_ds
    (b' := env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len + termCode.len) r4
    (by simp [termCode.hlen])
  have hbEq : env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len + termCode.len = b := by
    dsimp only [b, lay, inner, dryTailLay, solverTailLayout, dryInnerCodeSel, dryDeepSelectCode,
      env, solverTailInnerEnv]
    omega
  have hAt : p.HasAt b (dryDeepSelectProcs { env with innerBase := b }) := by
    have h1 := hAtRaw
    change p.HasAt (env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len + termCode.len)
      (dryDeepSelectProcs { env with
        innerBase := env.innerBase + 1 + initCode.len + coreCode.len + selectCode.len +
          termCode.len }) at h1
    rw [hbEq] at h1
    exact h1
  unfold dryDeepSelectProcs at hAt
  obtain ⟨hEntry, s1⟩ := hasAt_peel_ds (b' := b + 1) hAt (by simp)
  obtain ⟨hDeep, s2⟩ := hasAt_peel_ds (b' := b + 7) s1
    (by rw [dryDeepProcs_length, dryDeepCodeLen])
  obtain ⟨hWrap, s3⟩ := hasAt_peel_ds (b' := b + 23) s2 (by simp)
  obtain ⟨hDgRef, s4⟩ := hasAt_peel_ds (b' := b + 35) s3
    (by rw [dgRefillModule_length])
  obtain ⟨hHeap, s5⟩ := hasAt_peel_ds (b' := b + 57) s4
    (by rw [selectHeapOpsModule_length])
  obtain ⟨hPhi, hEval⟩ := hasAt_peel_ds (b' := b + 74) s5
    (by rw [selectPhiFillModule_length])
  have hScInit : env.scInit = lay.scInit := rfl
  have hScOp : ∀ j, env.scOp j = lay.scOp j := fun _ => rfl
  have hLastInit : env.lastInit = lay.lastInit := rfl
  have hOpsEq : env.opsBase = ops := rfl
  have hDeepGet (i : ℕ) (hi : i < 6) :
      p.procs[b + (1 + i)]? = some ((dryDeepProcs { env with innerBase := b + 1 })[i]'(by
        rw [dryDeepProcs_length, dryDeepCodeLen]; exact hi)) := by
    have h := hDeep.get (i := i) (by rw [dryDeepProcs_length, dryDeepCodeLen]; exact hi)
    rwa [Nat.add_assoc] at h
  have hWrapGet (i : ℕ) (hi : i < 16) :=
    hWrap.get (i := i) (by simpa using hi)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hDgRef, hHeap, hPhi, hEval⟩
  · simpa [hScOp] using hEntry.get (i := 0) (by simp)
  · simpa [dryDeepProcs, hScInit, hScOp, hLastInit, hOpsEq, Nat.add_assoc] using hDeepGet 0 (by omega)
  · simpa [dryDeepProcs] using hDeepGet 1 (by omega)
  · simpa [dryDeepProcs, Nat.add_assoc] using hDeepGet 2 (by omega)
  · simpa [dryDeepProcs, hOpsEq] using hDeepGet 3 (by omega)
  · simpa [dryDeepProcs] using hDeepGet 4 (by omega)
  · simpa [dryDeepProcs, hOpsEq] using hDeepGet 5 (by omega)
  · simpa [Nat.add_assoc] using hWrapGet 0 (by omega)
  · simpa [Nat.add_assoc] using hWrapGet 1 (by omega)
  · simpa [Nat.add_assoc] using hWrapGet 2 (by omega)
  · simpa [Nat.add_assoc] using hWrapGet 3 (by omega)
  · simpa [Nat.add_assoc, hScOp] using hWrapGet 4 (by omega)
  · simpa [Nat.add_assoc] using hWrapGet 5 (by omega)
  · simpa [Nat.add_assoc] using hWrapGet 6 (by omega)
  · simpa [Nat.add_assoc] using hWrapGet 7 (by omega)
  · simpa [Nat.add_assoc, hOpsEq] using hWrapGet 8 (by omega)
  · simpa [Nat.add_assoc] using hWrapGet 9 (by omega)
  · simpa [Nat.add_assoc] using hWrapGet 10 (by omega)
  · simpa [Nat.add_assoc] using hWrapGet 11 (by omega)
  · simpa [Nat.add_assoc] using hWrapGet 12 (by omega)
  · simpa [Nat.add_assoc] using hWrapGet 13 (by omega)
  · simpa [Nat.add_assoc] using hWrapGet 14 (by omega)
  · simpa [Nat.add_assoc] using hWrapGet 15 (by omega)

/-! ## 3. Helper contract transfers inside `dryLinkedProgramSel` -/

private theorem sparseCoreForestCapAt_mono_sel {w L depth k M N vCap eCap capExp fcap₁ fcap₂ : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ}
    (h : SparseCoreForestCapAt fmt L depth tool initialGraph k M N vCap eCap capExp P allocation
      fcap₁ R p op)
    (hle : fcap₁ ≤ fcap₂) :
    SparseCoreForestCapAt fmt L depth tool initialGraph k M N vCap eCap capExp P allocation
      fcap₂ R p op := by
  refine ⟨fun b a x args mem pos ω hargs hhead hrep hpre hfoot hz hroom => ?_⟩
  obtain ⟨body, hbody, o, st', c, x', hr, hrep', hF, hresp, hc⟩ :=
    h.op2_runs b a x args mem pos ω hargs hhead hrep hpre hfoot hz hroom
  obtain ⟨fv, fe, hLw, hLSF, hfEnd, hfFoot, hstEnd, hE1, hE2, hfCap⟩ := hF
  exact ⟨body, hbody, o, st', c, x', hr, hrep',
    ⟨fv, fe, hLw, hLSF, hfEnd, hfFoot, hstEnd, hE1, hE2, hfCap.trans hle⟩, hresp, hc⟩

private theorem readoutFoot_cast_ds {w : ℕ} {T₁ T₂ : SparseCoreRestartTool} (h : T₁ = T₂)
    {p : Program} {op : ℕ → ℕ} {L depth capExp : ℕ} {fmt : Num.Format w}
    {G : MGraph} {k M N vCap eCap : ℕ} {P : SparseCoreOrdParams} {alloc : ℕ → List ℕ → ℕ}
    (R : DSRep (SparseCoreOrdAbs T₂))
    (hfoot : SparseCoreReadoutFootAt fmt L depth T₂ G k M N vCap eCap capExp P alloc R p op) :
    SparseCoreReadoutFootAt fmt L depth T₁ G k M N vCap eCap capExp P alloc
      (h ▸ R : DSRep (SparseCoreOrdAbs T₁)) p op := by
  subst h; exact hfoot

/-- Per-level `SparseCoreForestCapAt` inside `dryLinkedProgramSel` (for any graph `G` with
`G.n ≤ G.m + 1`). -/
theorem drySC_forestCap_level_sel (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (selInitCode : SolverInnerSubCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (i : ℕ) (hi : i < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (G : MGraph) (hGn_le : G.n ≤ G.m + 1) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let lay := dryTailLay Psc.sc inner
    let limbMul := concreteReadout2LimbMul W
    let R := drySCRep Psc allocationCoefficient allocationDegree source J hw
    let p := dryLinkedProgramSel W Psc.sc inner selInitCode
    SparseCoreForestCapAt F.fmt F.limbs (dryDepth J) cfg.T G cfg.P.k
      (levelM cfg.TP cfg.P i) cfg.N₀ (namedInstance I).n (initTargetCap cfg (namedInstance I))
      dryCapExp (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)
      (dryDeepFCap J) R p lay.scOp := by
  intro W I V k F cfg lay limbMul R p
  let M₀ := max I.m (concreteEdgeThresholdWithLast W)
  let depth := Expander.chosenL (M₀ ^ 2)
  have hlim := dry_initTargetCap_le_capLimit J hJn hJm hCapPos
  have hdepth_le : depth ≤ levelM cfg.TP cfg.P i + cfg.N₀ + cfg.P.k + F.limbs := by
    have h1 : depth ≤ 4 * M₀ + 1 := chosenL_sq_le_four_mul_add_one cfg.P.hM₀
    have hN₀ : cfg.N₀ = 4 * M₀ := rfl
    have hk1 : 1 ≤ cfg.P.k := cfg.P.hk
    omega
  have hcap := concrete_sparseCoreCapHyp_uniform W J hJn hJm hCapPos i hi.le
    (namedInstance I).n (initTargetCap cfg (namedInstance I)) hlim
  have hInit : ∀ j < cfg.P.k,
      IsValidLSFInitFor (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed cfg.P.k j :=
    fun j hj => dryLSFInitUsed_isValidLSFInitFor F.limbs F.fmt.precision cfg.P.k j hj
  have hT : cfg.T = sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision)
      dryCLsstUsed depth sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool W sparsifyImplUsed rfl rfl rfl J hw
  have hHas : p.HasAt lay.scBase (shiftProgramProcs lay.scBase Psc.sc.prog) :=
    dryLinkedProgramSel_sc_hasAt W Psc.sc inner selInitCode
  have hEx := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    ((Classical.choose_spec (drySC_bridged_exists Psc)).2 dryCapExp limbMul))).2.2.2
    depth (dryWordSize W allocationCoefficient allocationDegree source) F.fmt F.limbs
    (Expander.one_le_chosenL _)
    (by dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega)
  have hCapSpec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hEx))
    (namedInstance I).n (initTargetCap cfg (namedInstance I))
  have hBoth := (Classical.choose_spec hCapSpec).2 G cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀
    (drySCSizeParam J) rfl hcap hdepth_le (chosenL_sq_le_bundleLogFactor cfg.P.hM₀ le_rfl)
    (MinCostFlow.SparseCore.Program.chosenL_sq_le_chosenL_add_sq le_rfl)
    (drySCSizeParam_ge J hJn hJm hCapPos i (namedInstance I).n (initTargetCap cfg (namedInstance I)) hlim)
    hInit hGn_le (drySC_k_le_capExp J i)
  have hFoot := readoutFoot_cast_ds hT _ (sparseCoreReadoutFootAt_shift hHas hBoth.2.1)
  refine sparseCoreForestCapAt_mono_sel ⟨hFoot.op2_runs⟩ ?_
  unfold dryDeepFCap dynGraphSize
  dsimp only
  have hsq : ((namedInstance I).n + initTargetCap cfg (namedInstance I) + 2) ^ 2 ≤
      (dryCapLimit W J) ^ 2 := Nat.pow_le_pow_left hlim 2
  dsimp only [W, I, cfg] at hlim hsq ⊢
  omega

/-- Last-level implementation inside `dryLinkedProgramSel` for every connected graph `G` with
`G.m ≤ I.m`, `G.m ≤ levelM cfg.TP cfg.P cfg.P.d`, and `G.n ≤ G.m + 1`. -/
theorem dryDeepSelectCode_hLastImpl_sel (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (selInitCode : SolverInnerSubCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let G0 := namedInstance I
    let w := dryWordSize W allocationCoefficient allocationDegree source
    let p := dryLinkedProgramSel W Psc.sc inner selInitCode
    let lay := dryTailLay Psc.sc inner
    ∀ G : MGraph, G.m ≤ I.m → G.m ≤ levelM cfg.TP cfg.P cfg.P.d → G.n ≤ G.m + 1 →
      (∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) →
      (LastLevelProgram.lastLevelRepresentation G0.n (initTargetCap cfg G0) 4 F.limbs
          F.fmt.precision G.E).Implements
        w p lay.lastInit lay.lastOp
        (lastLevelRuntimeMachineContract F.fmt F.limbs cfg.L G G0.n (initTargetCap cfg G0)
          (dryLastMult J) (dryLastStretchP J) (fun _ _ => dryLastSpace J)) := by
  intro W I V k F cfg G0 w p lay G hGmI hGmD hGnM hConn
  have hcapLim : G0.n + initTargetCap cfg G0 + 2 ≤ dryCapLimit W J :=
    dry_initTargetCap_le_capLimit J hJn hJm hCapPos
  refine lastLevelRuntime_implements_mono
    (dryLastBodies_implements (dryLinkedProgramSel_lastLevel_hasAt W Psc.sc inner selInitCode)
      F.fmt G rfl hConn hGnM) ?_ ?_ ?_
  · exact packedLastLevelMultiplier_le_dryLastMultBound
      (le_trans hGnM (Nat.add_le_add_right hGmD 1)) hGmD
  · have hsz := Nat.size_le_size (Nat.add_le_add_right hGmI 1)
    change (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (G.m + 1).size ≤
      (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (I.m + 1).size
    omega
  · intro args
    dsimp only [W] at hcapLim
    exact packedRuntimeAllocation_le_bound G lastGuest lastCanonConst
      (by omega) hGmI (by omega) (by omega) 1 args

/-! ## 4. Tight inner `ShiftDeepChainSyncSpecWExtKFBL` at `lay.shiftDeepChain + 1` -/

/-- **Tight inner `ShiftDeepChainSyncSpecWExtKFBL` inside `dryLinkedProgramSel`** for the
embedded `shiftDeepChainBodyKFBL` at `lay.shiftDeepChain + 1`, preserving the exact inner bounds
`dryDeepSpace Psc J`, `deepShiftFixedBound`, `deepShiftToolMulBound`, and
`wireTreeSyncEditCost + 2` (leaving full headroom for `dryDeepSelectSpace`, `dryDeepSelectFixed`,
and `shiftDeepSelectToolMulBound`). -/
theorem dryDeepSelectCode_hDeepInner (Psc : DrySparseCorePieces)
    (initCode coreCode selectCode termCode selInitCode : SolverInnerSubCode)
    (openSz : DryOpenSizes) (hOpen : DryOpenSizeBounds openSz)
    (selSz : DrySelectRebuildSizes) (hSel : DrySelectRebuildSizeBounds selSz) :
    let inner := dryInnerCodeSel initCode coreCode selectCode termCode dryDeepSelectCode
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let limbMul := concreteReadout2LimbMul dryWitnessUsed
      let PscP := drySCParams Psc dryCapExp limbMul
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      ShiftDeepChainSyncSpecWExtKFBL
        (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
        F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
        (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
        (dryCapLimit dryWitnessUsed J) PscP.wordExp
        (dryLastStretchP J) (dryDeepIntCapMax J) (dryDeepForestEdgeCap J)
        G.n (initTargetCap cfg G) cfg Rcore
        (dryLinkedProgramSel dryWitnessUsed Psc.sc inner selInitCode)
        ((dryTailLay Psc.sc inner).shiftDeepChain + 1)
        (dryDeepSpace Psc J)
        (deepShiftFixedBound PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d (dryLastMult J))
        (deepShiftToolMulBound F.limbs dryCapExp PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d
          (dryLastMult J))
        (wireTreeSyncEditCost F.limbs (detectOffTreeDrainUnit F.limbs) + 2) := by
  intro inner source J hJn hJm hCost hCap hw I V k F cfg G limbMul PscP Rcore
  let W := dryWitnessUsed
  let coeff := dryAllocCoeffConcrete Psc openSz hOpen selSz hSel
  let deg := dryAllocDegConcrete Psc openSz hOpen selSz hSel
  let w := dryWordSize W coeff deg source
  let p := dryLinkedProgramSel W Psc.sc inner selInitCode
  let lay := dryTailLay Psc.sc inner
  let b := lay.shiftDeepChain
  let ops := mrdsCycleBase
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hfit := ipm_quality_parameter_words_fit I.m V k hw
  have hw14 : 14 ≤ w := hfit.1
  have hw17 : 17 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 17 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hWidth : F.fmt.precision ≤ 4 * F.limbs := by
    change ipmQualityPrecision I.m V k ≤ 4 * ipmQualityLimbs I.m V k
    unfold ipmQualityLimbs; omega
  have hL4W : 4 * F.limbs + 2 < 2 ^ w := by
    have hB14 : 2 ^ 14 * ipmQualityParameterBound I.m V k < 2 ^ w := by
      have hsz : ipmQualityParameterBound I.m V k < 2 ^ (ipmQualityParameterBound I.m V k).size :=
        Nat.lt_size_self _
      calc 2 ^ 14 * ipmQualityParameterBound I.m V k
          < 2 ^ 14 * 2 ^ (ipmQualityParameterBound I.m V k).size :=
            Nat.mul_lt_mul_of_pos_left hsz (by decide)
        _ = 2 ^ (14 + (ipmQualityParameterBound I.m V k).size) := (pow_add 2 _ _).symm
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    have hLle : F.limbs ≤ ipmQualityParameterBound I.m V k := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityParameterBound]; omega
    have hB1 : 1 ≤ ipmQualityParameterBound I.m V k := by unfold ipmQualityParameterBound; omega
    omega
  have hWordCoeff : Classical.choose (concrete_solver_word_bounds_poly W) ≤ coeff :=
    (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨hQuotaBoundW, h4M3W⟩ :=
    Classical.choose_spec (concrete_solver_word_bounds_poly W)
      coeff deg hWordCoeff source J hJn hJm hCap1 hw
  have hN0W : cfg.N₀ < 2 ^ w :=
    lt_of_le_of_lt (by change 4 * cfg.P.M₀ ≤ 4 * cfg.P.M₀ + 3; omega) h4M3W
  have hDepthW : Expander.chosenL (cfg.P.M₀ ^ 2) < 2 ^ w := by
    have hM1 : 1 ≤ cfg.P.M₀ := le_trans (by decide : 1 ≤ 2)
      ((concreteEdgeThresholdWithLast_ge_two W).trans (le_max_right _ _))
    exact lt_of_le_of_lt ((chosenL_sq_le_four_mul_add_one hM1).trans
      (by change 4 * cfg.P.M₀ + 1 ≤ 4 * cfg.P.M₀ + 3; omega)) h4M3W
  have hkW : cfg.P.k < 2 ^ w := by
    have hpsi1 : 1 ≤ alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀ := by unfold alg2PsiGameNat; omega
    have h1 : cfg.P.k ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k := by
      unfold shiftQuotaBase; exact Nat.le_mul_of_pos_left _ (by omega)
    have h2 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ≤
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_self_pow (by omega) _
    have h3 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) ≤
        (2 * G.m + 2) * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact lt_of_le_of_lt ((h1.trans h2).trans h3) hQuotaBoundW
  have hdW : cfg.P.d < 2 ^ w := by
    have hpsi1 : 1 ≤ alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀ := by unfold alg2PsiGameNat; omega
    have h2b : 2 ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k := by
      unfold shiftQuotaBase
      have hk1 : 1 ≤ cfg.P.k := cfg.P.hk
      nlinarith
    have h1 : cfg.P.d < 2 ^ (cfg.P.d + 1) :=
      Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
    have h2 : 2 ^ (cfg.P.d + 1) ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.pow_le_pow_left h2b _
    have h3 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) ≤
        (2 * G.m + 2) * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact (h1.trans_le (h2.trans h3)).trans hQuotaBoundW
  have hOpsAt := dryLinkedProgramSel_ops_hasAt W Psc.sc inner selInitCode
  have hInitH := solverOpsProcs_initHelpers hw14 hOpsAt
  have hEvalH := solverOpsProcs_evalTermHelpers (L := F.limbs) (fmt := F.fmt) hw14 rfl hOpsAt
  obtain ⟨_, hDeepAt, hPackAt, hCoreLenAt, hEdgeAt, hBindAt, hCanonAt, _⟩ :=
    dryDeepSelectCode_hasAll Psc initCode coreCode selectCode termCode selInitCode
  have hcapLim : G.n + initTargetCap cfg G + 2 ≤ dryCapLimit W J :=
    dry_initTargetCap_le_capLimit J hJn hJm hCap1
  have hCore : DeepShiftCoreKFBL F.fmt F.limbs I.m G.n (initTargetCap cfg G) dryCapExp cfg PscP
      (drySCAlloc Psc dryCapExp limbMul J) Rcore p lay.scInit lay.scOp :=
    fun j hj H hH hHm =>
      drySC_coreKFBL_sel Psc inner selInitCode coeff deg source J hJn hJm hCap1 hw j hj H hH hHm
  have hFCap : DeepShiftForestCapKFBL F.fmt F.limbs G.n (initTargetCap cfg G) dryCapExp cfg PscP
      (drySCAlloc Psc dryCapExp limbMul J) (dryDeepFCap J) Rcore p lay.scOp :=
    fun j hj H hH =>
      drySC_forestCap_level_sel Psc inner selInitCode coeff deg source J hJn hJm hCap1 hw j hj H hH
  have hBindHasAt : p.HasAt (b + 5) [pathSlotBindBody] := by
    intro idx hidx
    have h0 : idx = 0 := by simp at hidx; omega
    subst h0; simpa using hBindAt
  have hOps := drySC_deepShiftOpsHypKFBL Psc coeff deg source J hJn hJm hCap1 hw
    (fcap := dryDeepFCap J) (lastMul := dryLastMult J)
    (intCapMax := dryDeepIntCapMax J) (forestEdgeCap := dryDeepForestEdgeCap J)
    (deepSpace := dryDeepSpace Psc J) (lastSpace := dryLastSpace J)
    (lastAlloc := fun _ _ => dryLastSpace J) (fun _ _ _ => le_rfl) le_rfl
  exact shiftDeepChainBody_meets_spec
    (w := w) (L := F.limbs) (P := F.fmt.precision) (m := I.m) (V := V)
    (psi := ⌈cfg.Ψ⌉₊) (k := k) (epsExp := k + Num.IPM.alphaExponent I.m V + 10)
    (drainUnit := detectOffTreeDrainUnit F.limbs) (capExp := dryCapExp) (limbMul := limbMul)
    (wordExp := PscP.wordExp) (stretchPrec := dryLastStretchP J) (lastMul := dryLastMult J)
    (intCapMax := dryDeepIntCapMax J) (forestEdgeCap := dryDeepForestEdgeCap J)
    (deepSpace := dryDeepSpace Psc J)
    (deepFixed := deepShiftFixedBound PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d (dryLastMult J))
    (toolMul := deepShiftToolMulBound F.limbs dryCapExp PscP (levelM cfg.TP cfg.P 0) cfg.N₀
      cfg.P.d (dryLastMult J))
    (vCap := G.n) (eCap := initTargetCap cfg G) (capLimit := dryCapLimit W J)
    (fcap := dryDeepFCap J) (restartSpace := dryDeepRestartSpace Psc J)
    (lastSpace := dryLastSpace J)
    (shiftDeepChainProc := b + 1) (initCore := lay.scInit) (coreLenProc := b + 3)
    (edgeProc := b + 4) (signExt := ops + 17) (mul := ops + 11) (intDiv := ops + 22)
    (copy := ops) (lastInit := lay.lastInit) (packEditsProc := b + 2)
    (initTree := ops + 81) (bind := b + 5) (canonCopy := b + 6) (isNeg := ops + 69)
    (fmt := F.fmt) (cfg := cfg) (Psc := PscP)
    (allocation := drySCAlloc Psc dryCapExp limbMul J)
    (lastAlloc := fun _ _ => dryLastSpace J)
    (Rcore := Rcore) (p := p)
    (opCore := lay.scOp) (opLast := lay.lastOp) (opTree := dryPathTreeOp ops)
    (dryDeepLevelSpace Psc J) (deepShiftLevelCost F.limbs dryCapExp cfg PscP)
    hDeepAt hPackAt
    (drySCRep_local Psc coeff deg source J hw)
    rfl rfl hWidth hL4W hw17 cfg.P.hk hkW hdW hN0W hDepthW
    (sparseCoreBundleRestartToolMachWith_initOrdEqOnE _ _ _ _ _ _)
    rfl hCore hFCap hcapLim
    (dryDeepSelectCode_hLastImpl_sel Psc inner selInitCode coeff deg source J hJn hJm hCap1 hw)
    hCoreLenAt hEdgeAt hInitH.2.2.2.2.1 hInitH.2.2.1 hInitH.2.2.2.2.2.2.1 hInitH.1
    hEvalH.2.2.2.2.2 (pathSlotBind_meetsContract hBindHasAt)
    (fun v => wireCanonCopy_meetsContract v hCanonAt hEvalH.1 hEvalH.2.2.1)
    hEvalH.2.2.2.2.1 hOps

end MinCostFlow.Final.DryRun

end
