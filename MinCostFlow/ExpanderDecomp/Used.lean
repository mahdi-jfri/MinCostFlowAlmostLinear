module

public import MinCostFlow.ExpanderDecomp.CoreOuter
public import MinCostFlow.ExpanderDecomp.ProgDecompEntry

/-!
# Assembly of `ExpanderDecompositionUsed` from `Core` and External Modules (`Used`)

Assembles a single Word-RAM program (`assembledDecompProg`) from:
1. the top-level entry procedure `decompEntryProc` (`ProgDecompEntry.lean`);
2. a multi-pair static router module (`MultiPairRouterModule`);
3. the concrete `Core` module `coreModuleProcs` (`CoreProg.lean`, containing `OneShot`, `Core`,
   `ProgCloud`, `ProgEdgeColor`, `ProgRemoveFake`, `ProgStepC`, and `ProgStepCLeftover`);
4. a Step B module (`StepBModule`);
5. the parameter-block writer `writeCoreParamsProc` (`CoreOuterParams.lean`) and outer-to-core
   adapter `coreAdapterProc` (`CoreOuter.lean`);
6. an outer-decomposition module (`OuterDecompModule`).

Proves `expanderDecompositionUsed_of_parts : ExpanderDecompositionUsed` via
`coreModule_meetsContract_B` (`CoreProg.lean`), `writeCoreParamsProc_meetsContract`
(`CoreOuterParams.lean`), `coreAdapterProc_meetsContract` (`CoreOuter.lean`), and
`expanderDecompositionUsed_of_outerContract` (`ProgDecompEntry.lean`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Relocatable Module Interfaces for External Parts -/

/-- A relocatable Word-RAM module implementing the multi-pair static router
(`multiPairRouterContract`, `ProgStepCSpec.lean`). When placed at `base`, procedure
`base + entryOff` meets `multiPairRouterContract C_rt C_sp w` for every word size `w`. -/
structure MultiPairRouterModule where
  /-- Procedure list placed at `base`. -/
  procs : ℕ → List Stmt
  /-- Offset of the router entry procedure from `base`. -/
  entryOff : ℕ
  /-- Cost multiplier constant in `multiPairRouterContract`. -/
  C_rt : ℕ
  /-- Heap-space multiplier constant in `multiPairRouterContract`. -/
  C_sp : ℕ
  /-- Contract proof for every placement `base` and word size `w`. -/
  meets : ∀ (base w : ℕ) (p : Program),
    p.HasAt base (procs base) →
    MeetsContract w p (base + entryOff) (multiPairRouterContract C_rt C_sp w)

/-- A relocatable Word-RAM module implementing Step B of `OneShot` (`ProgStepBSpec.stepBContract`)
against router constants `(C_rt, C_sp)`. When placed at `base` calling `coreOnIdx` and `routeIdx`,
procedure `base + entryOff` meets `stepBContract ParamConfig.default M r q w K_B S_B ...` for every
level `2 ≤ q ≤ r`, given `multiPairRouterContract` at `routeIdx` and the recursive `coreOnContract`
below level `q` at `coreOnIdx`. -/
structure StepBModule (C_rt C_sp : ℕ) where
  /-- Procedure list placed at `base`, calling `coreOnIdx` and `routeIdx`. -/
  procs : (base coreOnIdx routeIdx : ℕ) → List Stmt
  /-- Offset of the Step B entry procedure from `base`. -/
  entryOff : ℕ
  /-- Step-count multiplier `K_B` in `stepBContract`. -/
  K_B : ℕ
  /-- Heap-space multiplier `S_B` in `stepBContract`. -/
  S_B : ℕ
  /-- Contract proof for every placement, level `2 ≤ q ≤ r`, and word size `w`. -/
  meets : ∀ (base coreOnIdx routeIdx M r q w : ℕ) (p : Program),
    2 ≤ q → q ≤ r →
    p.HasAt base (procs base coreOnIdx routeIdx) →
    MeetsContract w p routeIdx (multiPairRouterContract C_rt C_sp w) →
    MeetsContract w p coreOnIdx
      ((coreOnContract ParamConfig.default M r w K_B
          (stepCTimeConst (C_rt + 2000) (C_rt + 1000)) S_B (stepCSpaceConst C_sp)).below
        (fun args _ => args.getD 0 0) q) →
    MeetsContract w p (base + entryOff)
      (stepBContract ParamConfig.default M r q w K_B S_B
        (coreProgTime K_B (stepCTimeConst (C_rt + 2000) (C_rt + 1000))
          ParamConfig.default M r (q - 1))
        (coreProgSpace S_B (stepCSpaceConst C_sp) ParamConfig.default M r (q - 1)))

/-- A relocatable Word-RAM module implementing the outer expander decomposition
(`ProgDecompEntrySpec.outerDecompEntryContract`), calling the outer-to-core adapter
(`coreAdapterContract`) at `coreAdapterIdx` and the single-pair static router
(`routeOrCutContract`) at `routeIdx`. -/
structure OuterDecompModule (K_B C_rt S_B C_sp_rt : ℕ) where
  /-- Procedure list placed at `base`, calling `coreAdapterIdx` and `routeIdx`. -/
  procs : (base coreAdapterIdx routeIdx : ℕ) → List Stmt
  /-- Offset of the outer entry procedure from `base`. -/
  entryOff : ℕ
  /-- Cost multiplier `K` in `outerDecompEntryContract K C_sp w`. -/
  K_out : ℕ
  /-- Heap-space multiplier `C_sp` in `outerDecompEntryContract K C_sp w`. -/
  C_sp_out : ℕ
  /-- Contract proof for every placement and word size `w`. -/
  meets : ∀ (base coreAdapterIdx routeIdx w : ℕ) (p : Program),
    p.HasAt base (procs base coreAdapterIdx routeIdx) →
    (∀ M r,
      MeetsContract w p coreAdapterIdx
        (coreAdapterContract M r (coreAdapterCost M r)
          (coreAdapterTimeConst K_B (C_rt + 2000) (C_rt + 1000))
          (coreAdapterSpaceConst S_B C_sp_rt) w)) →
    MeetsContract w p routeIdx (routeOrCutContract C_rt C_sp_rt w) →
    MeetsContract w p (base + entryOff) (outerDecompEntryContract K_out C_sp_out w)

/-! ## 2. Concrete Program Assembly -/

/-- The length of `coreModuleProcs` is independent of its base and external procedure indices. -/
lemma coreModuleProcs_length (base stepBIdx routeIdx : ℕ) :
    (coreModuleProcs base stepBIdx routeIdx).length = (coreModuleProcs 0 0 0).length := by
  simp [coreModuleProcs, cloudExpanderProcs, runner, removeFakeProcs]

/-- Assembled Word-RAM program laying out:
- `0`: `decompEntryProc bOuterEntry`
- `1`: `hRoute.procs 1`
- `bCore`: `coreModuleProcs bCore bStepBEntry bRouteEntry`
- `bStepBBase`: `hStepB.procs bStepBBase bCoreOn bRouteEntry`
- `bParams`: `writeCoreParamsProc`
- `bParams + 1`: `coreAdapterProc bParams idx.core`
- `bOuterBase`: `hOuterProg.procs bOuterBase (bParams + 1) bRouteEntry`. -/
def assembledDecompProg
    (hRoute : MultiPairRouterModule)
    (hStepB : StepBModule hRoute.C_rt hRoute.C_sp)
    (hOuterProg : OuterDecompModule hStepB.K_B hRoute.C_rt hStepB.S_B hRoute.C_sp) : Program :=
  let bRouteEntry := 1 + hRoute.entryOff
  let routeSeg := hRoute.procs 1
  let bCore := 1 + routeSeg.length
  let bStepBBase := bCore + (coreModuleProcs 0 0 0).length
  let bStepBEntry := bStepBBase + hStepB.entryOff
  let idx := coreModuleIdx bCore bStepBEntry bRouteEntry
  let coreSeg := coreModuleProcs bCore bStepBEntry bRouteEntry
  let stepBSeg := hStepB.procs bStepBBase idx.coreOn bRouteEntry
  let bParams := bStepBBase + stepBSeg.length
  let bAdapter := bParams + 1
  let adapterSeg := [writeCoreParamsProc, coreAdapterProc bParams idx.core]
  let bOuterBase := bParams + 2
  let bOuterEntry := bOuterBase + hOuterProg.entryOff
  let outerSeg := hOuterProg.procs bOuterBase bAdapter bRouteEntry
  ⟨[decompEntryProc bOuterEntry] ++ routeSeg ++ coreSeg ++ stepBSeg ++ adapterSeg ++ outerSeg⟩

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

private lemma hasAt_of_concat {p : Program} {k : ℕ} {pre seg suf : List Stmt}
    (hp : p.procs = pre ++ seg ++ suf) (hk : pre.length = k) :
    p.HasAt k seg := by
  intro i hi
  subst hk
  have h1 : pre.length + i < (pre ++ seg).length := by simp; omega
  have h2 : pre.length + i < (pre ++ seg ++ suf).length := by simp; omega
  rw [hp, List.getElem?_eq_getElem h2, List.getElem_append_left h1,
    List.getElem_append_right (Nat.le_add_right pre.length i)]
  simp

/-- If the three external modules are deterministic (`NoRand`), then every procedure in
`assembledDecompProg` is deterministic (`NoRand`). -/
theorem assembledDecompProg_noRand
    (hRoute : MultiPairRouterModule)
    (hStepB : StepBModule hRoute.C_rt hRoute.C_sp)
    (hOuterProg : OuterDecompModule hStepB.K_B hRoute.C_rt hStepB.S_B hRoute.C_sp)
    (hRouteNR : ∀ b s, s ∈ hRoute.procs b → s.NoRand)
    (hStepBNR : ∀ b c r s, s ∈ hStepB.procs b c r → s.NoRand)
    (hOuterNR : ∀ b c r s, s ∈ hOuterProg.procs b c r → s.NoRand) :
    ∀ s ∈ (assembledDecompProg hRoute hStepB hOuterProg).procs, s.NoRand := by
  intro s hs
  unfold assembledDecompProg at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with ((((rfl | h1) | h2) | h3) | (rfl | rfl)) | h4
  · exact decompEntryProc_noRand _
  · exact hRouteNR _ s h1
  · exact coreModuleProcs_noRand _ _ _ s h2
  · exact hStepBNR _ _ _ s h3
  · exact writeCoreParamsProc_noRand
  · exact coreAdapterProc_noRand _ _
  · exact hOuterNR _ _ _ s h4

/-! ## 3. Path to `ExpanderDecompositionUsed` -/

/-- **Path to `ExpanderDecompositionUsed` from concrete `Core`, its outer adapter, and external
modules:** given a multi-pair static router module (`hRoute`), a Step B module (`hStepB`), and an
outer-decomposition module (`hOuterProg`), `assembledDecompProg` together with
`coreModule_meetsContract_B`, `writeCoreParamsProc_meetsContract`, `coreAdapterProc_meetsContract`,
and `expanderDecompositionUsed_of_outerContract` yields `ExpanderDecompositionUsed`. -/
theorem expanderDecompositionUsed_of_parts
    (hRoute : MultiPairRouterModule)
    (hStepB : StepBModule hRoute.C_rt hRoute.C_sp)
    (hOuterProg : OuterDecompModule hStepB.K_B hRoute.C_rt hStepB.S_B hRoute.C_sp) :
    ExpanderDecompositionUsed := by
  set bRouteEntry := 1 + hRoute.entryOff
  set routeSeg := hRoute.procs 1
  set bCore := 1 + routeSeg.length
  set bStepBBase := bCore + (coreModuleProcs 0 0 0).length
  set bStepBEntry := bStepBBase + hStepB.entryOff
  set idx := coreModuleIdx bCore bStepBEntry bRouteEntry
  set coreSeg := coreModuleProcs bCore bStepBEntry bRouteEntry
  set stepBSeg := hStepB.procs bStepBBase idx.coreOn bRouteEntry
  set bParams := bStepBBase + stepBSeg.length
  set bAdapter := bParams + 1
  set adapterSeg := [writeCoreParamsProc, coreAdapterProc bParams idx.core]
  set bOuterBase := bParams + 2
  set bOuterEntry := bOuterBase + hOuterProg.entryOff
  set outerSeg := hOuterProg.procs bOuterBase bAdapter bRouteEntry
  set P : Program := assembledDecompProg hRoute hStepB hOuterProg
  have hP_eq : P.procs =
      [decompEntryProc bOuterEntry] ++ routeSeg ++ coreSeg ++ stepBSeg ++ adapterSeg ++
        outerSeg := rfl
  have hCoreLen : coreSeg.length = (coreModuleProcs 0 0 0).length :=
    coreModuleProcs_length bCore bStepBEntry bRouteEntry
  have hHasEntry : P.HasAt 0 [decompEntryProc bOuterEntry] :=
    hasAt_of_concat (pre := []) (seg := [decompEntryProc bOuterEntry])
      (suf := routeSeg ++ coreSeg ++ stepBSeg ++ adapterSeg ++ outerSeg)
      (by simp [hP_eq, List.append_assoc]) rfl
  have hHasRoute : P.HasAt 1 routeSeg :=
    hasAt_of_concat (pre := [decompEntryProc bOuterEntry]) (seg := routeSeg)
      (suf := coreSeg ++ stepBSeg ++ adapterSeg ++ outerSeg)
      (by simp [hP_eq, List.append_assoc]) rfl
  have hHasCore : P.HasAt bCore coreSeg :=
    hasAt_of_concat (pre := [decompEntryProc bOuterEntry] ++ routeSeg) (seg := coreSeg)
      (suf := stepBSeg ++ adapterSeg ++ outerSeg)
      (by simp [hP_eq, List.append_assoc]) (by simp [bCore]; omega)
  have hHasStepB : P.HasAt bStepBBase stepBSeg :=
    hasAt_of_concat (pre := [decompEntryProc bOuterEntry] ++ routeSeg ++ coreSeg) (seg := stepBSeg)
      (suf := adapterSeg ++ outerSeg)
      (by simp [hP_eq, List.append_assoc]) (by simp [bStepBBase, bCore, hCoreLen]; omega)
  have hHasAdapter : P.HasAt bParams adapterSeg :=
    hasAt_of_concat
      (pre := [decompEntryProc bOuterEntry] ++ routeSeg ++ coreSeg ++ stepBSeg)
      (seg := adapterSeg) (suf := outerSeg)
      (by simp [hP_eq, List.append_assoc])
      (by simp [bParams, bStepBBase, bCore, hCoreLen]; omega)
  have hHasOuter : P.HasAt bOuterBase outerSeg :=
    hasAt_of_concat
      (pre := [decompEntryProc bOuterEntry] ++ routeSeg ++ coreSeg ++ stepBSeg ++ adapterSeg)
      (seg := outerSeg) (suf := [])
      (by simp [hP_eq, List.append_assoc])
      (by simp [bOuterBase, bParams, bStepBBase, bCore, hCoreLen, adapterSeg]; omega)
  have hParamsProc : P.procs[bParams]? = some writeCoreParamsProc := by
    simpa [adapterSeg] using hHasAdapter 0 (by simp [adapterSeg])
  have hAdapterProc : P.procs[bAdapter]? = some (coreAdapterProc bParams idx.core) := by
    simpa [adapterSeg, bAdapter] using hHasAdapter 1 (by simp [adapterSeg])
  refine expanderDecompositionUsed_of_outerContract (K := hOuterProg.K_out)
      (C_sp := hOuterProg.C_sp_out) hHasEntry (fun w => ?_)
  have hRoute_w : MeetsContract w P bRouteEntry
      (multiPairRouterContract hRoute.C_rt hRoute.C_sp w) :=
    hRoute.meets 1 w P hHasRoute
  have hRoute1_w : MeetsContract w P bRouteEntry
      (routeOrCutContract hRoute.C_rt hRoute.C_sp w) :=
    multiPairRouterContract_implies_routeOrCutContract hRoute_w
  have hParams_w : MeetsContract w P bParams (writeCoreParamsContract w) :=
    writeCoreParamsProc_meetsContract hParamsProc
  have hAdapter_w : ∀ M r,
      MeetsContract w P bAdapter
        (coreAdapterContract M r (coreAdapterCost M r)
          (coreAdapterTimeConst hStepB.K_B (hRoute.C_rt + 2000) (hRoute.C_rt + 1000))
          (coreAdapterSpaceConst hStepB.S_B hRoute.C_sp) w) := by
    intro M r
    have hCore_w : MeetsContract w P idx.core
        (coreEntryContract ParamConfig.default M r w
          hStepB.K_B (hRoute.C_rt + 2000) (hRoute.C_rt + 1000) hStepB.S_B hRoute.C_sp) :=
      coreModule_meetsContract_B hHasCore hRoute_w (fun q hq2 hqr hSub =>
        hStepB.meets bStepBBase idx.coreOn bRouteEntry M r q w P hq2 hqr hHasStepB hRoute_w hSub)
    exact coreAdapterProc_meetsContract hAdapterProc hParams_w hCore_w
  exact hOuterProg.meets bOuterBase bAdapter bRouteEntry w P hHasOuter hAdapter_w hRoute1_w

end MinCostFlow.ExpanderDecomp
