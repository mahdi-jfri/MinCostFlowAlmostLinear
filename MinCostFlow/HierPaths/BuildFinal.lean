module

public import MinCostFlow.HierPaths.BuildProgLevel
public import MinCostFlow.HierPaths.BuildCoreBridge
public import MinCostFlow.HierPaths.BuildRouterBridge
public import MinCostFlow.HierPaths.BuildTopChain
public import MinCostFlow.ExpanderDecomp.Used
public import MinCostFlow.ExpanderDecomp.UsedProved
public import MinCostFlow.ExpanderDecomp.ProgStepB
public import MinCostFlow.ExpanderDecomp.RouteProgEntry
import MinCostFlow.HierPaths.BuildProgSpacePoly
import MinCostFlow.HierPaths.InitProgCompleteCost
import MinCostFlow.HierPaths.QueryProgSpec
import MinCostFlow.HierPaths.DelProgSpec

/-!
# End-to-End Static Hierarchy Assembly from the Static Router (`BuildFinal`)

Assembles the complete deterministic level procedure `buildFinalLevelProc : HierProc` from:
1. the one-parent level builder `buildLevelProcs` (`BuildProgLevel.lean`),
2. the bump-heap core bridge `coreBridgeProcs` (`BuildCoreBridge.lean`),
3. the outer-to-core adapter `[writeCoreParamsProc, coreAdapterProc]` (`CoreOuterParams.lean`,
   `CoreOuter.lean`),
4. the concrete recursive cut player `coreModuleProcs` (`CoreProg.lean`),
5. the concrete Step B module `stepBModule` (`ProgStepB.lean`),
6. the static router modules (`hCoreRoute : MultiPairRouterModule` for `Core`, and
   `hHierRoute : HierRouterModule` with walks for `buildLevelProcs`).

Why both router interfaces appear: `RouterProcContract` (`BuildProgContracts.lean`) allows cost
`K * (routeCost + G.encode.length + ...)` and space `sR G.encode.length ...`, whereas
`multiPairRouterContract` (`ProgStepCSpec.lean`) forbids `G.m` in the cost when `e_X ≪ G.m` and
uses `outerRouterSpace C_sp G.n (routeOrCutCost ...)`. The top-level router procedure with walks
(`RouteProg.lean`, `RouteProgEntry.lean`) instantiates both `hCoreRoute` (through its implication
to `multiPairRouterContract`) and `hHierRoute` (through the router bridge
`BuildRouterBridge.lean`). `hierPathDSExistsFrom` uses this procedure.

Main results:
* `HierRouterModule`: relocatable deterministic walk-producing router meeting `ProvidesRouter`,
  `IsMatchingPlayer`, `RouteCostLe`, and a polynomial space envelope.
* `buildFinalLevelProc_noRand`: determinism (`NoRand`).
* `buildFinalLevelProc_providesBuildLevel`: meets `ProvidesBuildLevel` for every `w`, `p`, `j`, `k`.
* `buildFinalLevelSpace_poly`: meets `BuildLevelSpacePoly` via `buildLevelSpace_poly_coreBridge`.
* `hierPathDSExistsFrom_of_routers`: `HierPathDSExistsFrom buildTopMinA` parameterized only by
  the router.
* `exists_pathDS_for_chain_of_routers`, `theorem_8_1_concrete_of_routers`, and
  `theorem_8_1_concrete_with_time_of_routers`: end-to-end corollaries for the chain of Section 8 of the paper.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp MinCostFlow.Expander

/-! ## 1. Relocatable Walk-Producing Router Module -/

/-- A relocatable deterministic Word-RAM module implementing the walk-producing static matching
player (`ProvidesRouter`) with abstract guarantees `IsMatchingPlayer`, `RouteCostLe`, and a
polynomial space envelope. Every constant is independent of the input graph and parameters. -/
structure HierRouterModule where
  /-- Procedure list placed at `base`. -/
  procs : ℕ → List Stmt
  /-- Offset of the router entry procedure from `base`. -/
  entryOff : ℕ
  /-- Determinism (`NoRand`) of every procedure in the module. -/
  noRand : ∀ base s, s ∈ procs base → s.NoRand
  /-- Abstract router function implemented by the module. -/
  route : RouterFn
  /-- Abstract router operation-count function. -/
  routeCost : RouterCostFn
  /-- Scratch-space envelope as a function of `(G.n, |G|, |pairs|, Δ + L + b + z)`. -/
  sR : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- Machine time multiplier in `ProvidesRouter`. -/
  K_rt : ℕ
  /-- Model operation-count constant in `RouteCostLe`. -/
  C_rt : ℕ
  /-- Polynomial space multiplier for `sR`. -/
  Cr : ℕ
  /-- Polynomial space exponent for `sR`. -/
  cr : ℕ
  /-- Abstract matching-player correctness. -/
  isPlayer : IsMatchingPlayer route routeCost
  /-- Abstract router operation-count bound. -/
  costLe : RouteCostLe routeCost C_rt
  /-- Polynomial space envelope on `sR`. -/
  spacePoly : ∀ n gLen pLen par, sR n gLen pLen par ≤ Cr * (n + gLen + pLen + par + 2) ^ cr
  /-- Contract proof for every placement `base` and word size `w`. -/
  meets : ∀ (base w : ℕ) (p : Program),
    p.HasAt base (procs base) →
    ProvidesRouter w K_rt route routeCost sR p (base + entryOff)

/-! ## 2. Concrete Level Procedure Assembly (`buildFinalLevelProc`) -/

/-- Wrapper entry body calling `buildLevelEntryProc` at index `k` with all 12 level arguments
`r0..r11` and returning its result. Allows `PL.At p j k` for arbitrary `(j, k)`. -/
def buildLevelEntryWrap (k : ℕ) : Stmt :=
  .call 12 k (List.range 12 |>.map Expr.reg) ;; .ret (.reg 12)

/-- Time multiplier constant of the assembled `coreAdapterProc` (from `stepBModule` and
`hCoreRoute`). -/
def finalCoreTimeConst (hCoreRoute : MultiPairRouterModule) : ℕ :=
  coreAdapterTimeConst (stepBTimeConst hCoreRoute.C_rt)
    (hCoreRoute.C_rt + 2000) (hCoreRoute.C_rt + 1000)

/-- Space multiplier constant of the assembled `coreAdapterProc` (from `stepBModule` and
`hCoreRoute`). -/
def finalCoreSpaceConst (hCoreRoute : MultiPairRouterModule) : ℕ :=
  coreAdapterSpaceConst (stepBSpaceConst hCoreRoute.C_sp) hCoreRoute.C_sp

/-- Common player time multiplier `K` shared by `hHierRoute` and `coreBridgeProcs`. -/
def finalPlayerK (hHierRoute : HierRouterModule) (hCoreRoute : MultiPairRouterModule) : ℕ :=
  max hHierRoute.K_rt (finalCoreTimeConst hCoreRoute + 500)

/-- Multiplicative time constant in `ProvidesBuildLevel` for `buildFinalLevelProc`. -/
def finalLevelK (hHierRoute : HierRouterModule) (hCoreRoute : MultiPairRouterModule) : ℕ :=
  buildLevelConst (finalPlayerK hHierRoute hCoreRoute) hHierRoute.C_rt + 20

/-- Scratch and output space function for `buildFinalLevelProc`. -/
def finalLevelSpace (hHierRoute : HierRouterModule) (hCoreRoute : MultiPairRouterModule) :
    Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ :=
  buildLevelSpace hHierRoute.sR (coreBridgeSpace (finalCoreSpaceConst hCoreRoute))

/-- Complete relocatable level procedure `HierProc`, assembling:
- `k .. k + 59`: `buildLevelProcs k bHierRouterEntry bBridge` (60 procedures),
- `k + 60 .. k + 62`: `coreBridgeProcs (k + 60) (k + 64)` (3 procedures),
- `k + 63 .. k + 64`: `[writeCoreParamsProc, coreAdapterProc (k + 63) idx.core]` (2 procedures),
- `k + 65 .. bStepB - 1`: `coreModuleProcs (k + 65) bStepB bCoreRouterEntry`,
- `bStepB`: `stepBModule` (1 procedure),
- `bCoreRouter ..`: `hCoreRoute.procs bCoreRouter`,
- `bHierRouter ..`: `hHierRoute.procs bHierRouter`. -/
noncomputable def buildFinalLevelProc
    (hHierRoute : HierRouterModule)
    (hCoreRoute : MultiPairRouterModule) : HierProc where
  entry k := buildLevelEntryWrap k
  helpers k :=
    let bBridge := k + 60
    let bParams := bBridge + 3
    let bAdapter := bParams + 1
    let bCore := bParams + 2
    let bStepB := bCore + (coreModuleProcs 0 0 0).length
    let bCoreRouter := bStepB + 1
    let bCoreRouterEntry := bCoreRouter + hCoreRoute.entryOff
    let coreRouterSeg := hCoreRoute.procs bCoreRouter
    let bHierRouter := bCoreRouter + coreRouterSeg.length
    let bHierRouterEntry := bHierRouter + hHierRoute.entryOff
    let hierRouterSeg := hHierRoute.procs bHierRouter
    let idx := coreModuleIdx bCore bStepB bCoreRouterEntry
    let levelSeg := buildLevelProcs k bHierRouterEntry bBridge
    let bridgeSeg := coreBridgeProcs bBridge bAdapter
    let adapterSeg := [writeCoreParamsProc, coreAdapterProc bParams idx.core]
    let coreSeg := coreModuleProcs bCore bStepB bCoreRouterEntry
    let stepBSeg := (stepBModule hCoreRoute.C_rt hCoreRoute.C_sp).procs bStepB idx.coreOn
      bCoreRouterEntry
    levelSeg ++ bridgeSeg ++ adapterSeg ++ coreSeg ++ stepBSeg ++ coreRouterSeg ++ hierRouterSeg

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp MinCostFlow.Expander

/-! ## 3. Helper Lemmas (List Splitting, Monotonicity, Wrapper) -/

private lemma buildLevelProcs_length (b router core : ℕ) :
    (buildLevelProcs b router core).length = 60 := by
  simp [buildLevelProcs, buildGameProcs, buildLevelTailProcs]

private lemma coreBridgeProcs_length (base fAdapter : ℕ) :
    (coreBridgeProcs base fAdapter).length = 3 := by
  simp [coreBridgeProcs]

private lemma hasAt_split_program {p : Program} {k : ℕ} {seg : List Stmt}
    (hne : 0 < seg.length) (h : p.HasAt k seg) :
    p.procs = p.procs.take k ++ seg ++ p.procs.drop (k + seg.length) ∧
      (p.procs.take k).length = k := by
  have hlast := h (seg.length - 1) (by omega)
  have hbound : k + seg.length ≤ p.procs.length := by
    have hlt := (List.getElem?_eq_some_iff.mp hlast).1
    omega
  have htake : (p.procs.take k).length = k := List.length_take_of_le (by omega)
  refine ⟨?_, htake⟩
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp [htake]; omega
  · by_cases hi1 : i < k
    · have hi1' : i < (p.procs.take k ++ seg).length := by simp [htake]; omega
      rw [List.getElem_append_left hi1', List.getElem_append_left (by omega : i < (p.procs.take k).length),
        List.getElem_take]
    · by_cases hi2 : i < k + seg.length
      · have hi2' : i < (p.procs.take k ++ seg).length := by simp [htake]; omega
        rw [List.getElem_append_left hi2',
          List.getElem_append_right (by omega : (p.procs.take k).length ≤ i)]
        have hget := h (i - k) (by omega)
        have hidx : k + (i - k) = i := by omega
        rw [hidx, List.getElem?_eq_getElem h1] at hget
        have hval := Option.some.inj hget
        simpa [htake] using hval
      · rw [List.getElem_append_right (by simp [htake]; omega), List.getElem_drop]
        congr 1
        simp [htake]; omega

private lemma providesRouter_mono_K {w K₁ K₂ f : ℕ} {route : RouterFn}
    {routeCost : RouterCostFn} {sR : ℕ → ℕ → ℕ → ℕ → ℕ} {p : Program}
    (hK : K₁ ≤ K₂) (h : ProvidesRouter w K₁ route routeCost sR p f) :
    ProvidesRouter w K₂ route routeCost sR p f := by
  intro G X pairs args mem pos ω hwords hpre
  obtain ⟨body, hf, o, st', c, hrun, hpost, hcost⟩ := h G X pairs args mem pos ω hwords hpre
  refine ⟨body, hf, o, st', c, hrun, hpost, le_trans hcost ?_⟩
  simp only [RouterProcContract, heapContract]
  exact Nat.mul_le_mul_right _ hK

private lemma providesCore_mono_K {w K₁ K₂ M r f : ℕ} {coreCost : ℕ → Graph → ℕ}
    {sC : ℕ → ℕ} {p : Program}
    (hK : K₁ ≤ K₂) (h : ProvidesCore w K₁ M r coreCost sC p f) :
    ProvidesCore w K₂ M r coreCost sC p f := by
  intro q G args mem pos ω hwords hpre
  obtain ⟨body, hf, o, st', c, hrun, hpost, hcost⟩ := h q G args mem pos ω hwords hpre
  refine ⟨body, hf, o, st', c, hrun, hpost, le_trans hcost ?_⟩
  simp only [CoreProcContract, heapContract]
  exact Nat.mul_le_mul_right _ hK

private lemma buildLevelEntryWrap_noRand (k : ℕ) : (buildLevelEntryWrap k).NoRand := by
  simp [buildLevelEntryWrap, Stmt.NoRand]

private lemma buildLevelEntryWrap_providesBuildLevel {w K j k : ℕ}
    {space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {p : Program}
    (hj : p.procs[j]? = some (buildLevelEntryWrap k))
    (hk : ProvidesBuildLevel w K space p k) :
    ProvidesBuildLevel w (K + 20) space p j := by
  intro G start s k' M r Δ L L' bh
  refine meetsContract_of_runs hj fun args mem pos ω hwords hpre => ?_
  have hpre_k : (buildLevelContract w K space G start s k' M r Δ L L' bh).pre args mem := hpre
  obtain ⟨⟨g, x, h, rfl, _⟩, _, _⟩ := hpre
  have hEval : evalArgs w (startState (buildLevelArgs g x start s k' M r Δ L L' bh h) mem pos)
      (List.range 12 |>.map Expr.reg) =
      some (buildLevelArgs g x start s k' M r Δ L L' bh h) := by
    simp [List.range_succ, evalArgs, Expr.eval, startState, buildLevelArgs]
  have hArgs12 : argsSize (List.range 12 |>.map Expr.reg) = 12 := by
    simp [List.range_succ, argsSize, Expr.size]
  refine runs_start_le ?_
  unfold buildLevelEntryWrap
  refine runs_seq_call_le (hk G start s k' M r Δ L L' bh) hEval hwords hpre_k ?_
  intro v mem' pos' hpost
  refine runs_ret_le (v := v) (Expr.eval_reg_of_eq (by simp)) hpost ?_
  simp only [buildLevelContract, heapContract, buildLevelCost, Expr.size]
  rw [hArgs12]
  set inner := buildLevelDegree L' * (s * k') *
      ((NOf M r) ^ 2 * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) +
        buildLevelDegree L' + 1) +
      (buildLevelDegree L' * k' + k' * k' + 1) * (s * k' + G.m + 1) *
        (routePathLen Δ bh L + 1) * (routeCong Δ bh L + 1) + k' * k' + 1
  have hinner : 1 ≤ inner := by dsimp only [inner]; omega
  rw [Nat.add_mul]
  have h20 : 20 ≤ 20 * inner := Nat.le_mul_of_pos_right 20 hinner
  omega

/-! ## 4. Main Theorems for `buildFinalLevelProc` and `HierPathDSExistsFrom` -/

/-- Every procedure in `buildFinalLevelProc` is deterministic (`NoRand`) whenever `hCoreRoute`
is deterministic. -/
theorem buildFinalLevelProc_noRand
    (hHierRoute : HierRouterModule)
    (hCoreRoute : MultiPairRouterModule)
    (hCoreRouteNR : ∀ b s, s ∈ hCoreRoute.procs b → s.NoRand) :
    (buildFinalLevelProc hHierRoute hCoreRoute).NoRand := by
  intro k
  refine ⟨buildLevelEntryWrap_noRand k, ?_⟩
  intro s hs
  simp only [buildFinalLevelProc, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hs
  rcases hs with (((((hLvl | hBr) | (rfl | rfl)) | hCore) | hSB) | hCR) | hHR
  · exact buildLevelProcs_noRand _ _ _ s hLvl
  · exact coreBridgeProcs_noRand _ _ s hBr
  · exact writeCoreParamsProc_noRand
  · exact coreAdapterProc_noRand _ _
  · exact coreModuleProcs_noRand _ _ _ s hCore
  · exact stepBModule_noRand hCoreRoute.C_rt hCoreRoute.C_sp _ _ _ s hSB
  · exact hCoreRouteNR _ s hCR
  · exact hHierRoute.noRand _ s hHR

/-- `buildFinalLevelProc` meets `ProvidesBuildLevel` for every word size `w` and placement
`(j, k)` with constants depending solely on `hHierRoute` and `hCoreRoute`. -/
theorem buildFinalLevelProc_providesBuildLevel
    (hHierRoute : HierRouterModule)
    (hCoreRoute : MultiPairRouterModule) :
    ∀ w p j k, (buildFinalLevelProc hHierRoute hCoreRoute).At p j k →
      ProvidesBuildLevel w (finalLevelK hHierRoute hCoreRoute)
        (finalLevelSpace hHierRoute hCoreRoute) p j := by
  intro w p j k ⟨hj, hk⟩
  set bBridge := k + 60
  set bParams := bBridge + 3
  set bAdapter := bParams + 1
  set bCore := bParams + 2
  set bStepB := bCore + (coreModuleProcs 0 0 0).length
  set bCoreRouter := bStepB + 1
  set bCoreRouterEntry := bCoreRouter + hCoreRoute.entryOff
  set coreRouterSeg := hCoreRoute.procs bCoreRouter
  set bHierRouter := bCoreRouter + coreRouterSeg.length
  set bHierRouterEntry := bHierRouter + hHierRoute.entryOff
  set hierRouterSeg := hHierRoute.procs bHierRouter
  set idx := coreModuleIdx bCore bStepB bCoreRouterEntry
  set levelSeg := buildLevelProcs k bHierRouterEntry bBridge
  set bridgeSeg := coreBridgeProcs bBridge bAdapter
  set adapterSeg := [writeCoreParamsProc, coreAdapterProc bParams idx.core]
  set coreSeg := coreModuleProcs bCore bStepB bCoreRouterEntry
  set stepBSeg := (stepBModule hCoreRoute.C_rt hCoreRoute.C_sp).procs bStepB idx.coreOn
    bCoreRouterEntry
  have hLvlLen : levelSeg.length = 60 := buildLevelProcs_length k bHierRouterEntry bBridge
  have hBrLen : bridgeSeg.length = 3 := coreBridgeProcs_length bBridge bAdapter
  have hAdLen : adapterSeg.length = 2 := rfl
  have hCoreLen : coreSeg.length = (coreModuleProcs 0 0 0).length :=
    coreModuleProcs_length bCore bStepB bCoreRouterEntry
  have hSBLen : stepBSeg.length = 1 := rfl
  -- Slice `p.HasAt k (helpers k)` into the seven segments
  have h6 : p.HasAt k (levelSeg ++ bridgeSeg ++ adapterSeg ++ coreSeg ++ stepBSeg ++ coreRouterSeg) :=
    hasAt_append_left hk
  have h5 : p.HasAt k (levelSeg ++ bridgeSeg ++ adapterSeg ++ coreSeg ++ stepBSeg) :=
    hasAt_append_left h6
  have h4 : p.HasAt k (levelSeg ++ bridgeSeg ++ adapterSeg ++ coreSeg) := hasAt_append_left h5
  have h3 : p.HasAt k (levelSeg ++ bridgeSeg ++ adapterSeg) := hasAt_append_left h4
  have h2 : p.HasAt k (levelSeg ++ bridgeSeg) := hasAt_append_left h3
  have hHasLvl : p.HasAt k levelSeg := hasAt_append_left h2
  have hHasBr : p.HasAt bBridge bridgeSeg := by
    simpa [bBridge, hLvlLen] using hasAt_append_right h2
  have hHasAd : p.HasAt bParams adapterSeg := by
    simpa [bParams, bBridge, hLvlLen, hBrLen, Nat.add_assoc] using hasAt_append_right h3
  have hHasCore : p.HasAt bCore coreSeg := by
    simpa [bCore, bParams, bBridge, hLvlLen, hBrLen, hAdLen, Nat.add_assoc] using
      hasAt_append_right h4
  have hHasSB : p.HasAt bStepB stepBSeg := by
    have h := hasAt_append_right h5
    rwa [show k + (levelSeg ++ bridgeSeg ++ adapterSeg ++ coreSeg).length = bStepB by
      simp [bStepB, bCore, bParams, bBridge, hLvlLen, hBrLen, hAdLen, hCoreLen]; omega] at h
  have hHasCR : p.HasAt bCoreRouter coreRouterSeg := by
    have h := hasAt_append_right h6
    rwa [show k + (levelSeg ++ bridgeSeg ++ adapterSeg ++ coreSeg ++ stepBSeg).length = bCoreRouter by
      simp [bCoreRouter, bStepB, bCore, bParams, bBridge, hLvlLen, hBrLen, hAdLen, hCoreLen,
        hSBLen]; omega] at h
  have hHasHR : p.HasAt bHierRouter hierRouterSeg := by
    have h := hasAt_append_right (show p.HasAt k ((levelSeg ++ bridgeSeg ++ adapterSeg ++
      coreSeg ++ stepBSeg ++ coreRouterSeg) ++ hierRouterSeg) from hk)
    rwa [show k + (levelSeg ++ bridgeSeg ++ adapterSeg ++ coreSeg ++ stepBSeg ++ coreRouterSeg).length =
      bHierRouter by
      simp [bHierRouter, bCoreRouter, bStepB, bCore, bParams, bBridge, hLvlLen, hBrLen, hAdLen,
        hCoreLen, hSBLen]; omega] at h
  -- 1. Core adapter contract from `hCoreRoute`, `stepBModule`, `coreModuleProcs`, `coreAdapterProc`
  have hParamsProc : p.procs[bParams]? = some writeCoreParamsProc := by
    simpa [adapterSeg] using hHasAd 0 (by simp [adapterSeg])
  have hAdapterProc : p.procs[bAdapter]? = some (coreAdapterProc bParams idx.core) := by
    simpa [adapterSeg, bAdapter] using hHasAd 1 (by simp [adapterSeg])
  have hCoreRouter : MeetsContract w p bCoreRouterEntry
      (multiPairRouterContract hCoreRoute.C_rt hCoreRoute.C_sp w) :=
    hCoreRoute.meets bCoreRouter w p hHasCR
  have hParams_w : MeetsContract w p bParams (writeCoreParamsContract w) :=
    writeCoreParamsProc_meetsContract hParamsProc
  have hAdapter_w : ∀ M r,
      MeetsContract w p bAdapter
        (coreAdapterContract M r (coreAdapterCost M r)
          (finalCoreTimeConst hCoreRoute) (finalCoreSpaceConst hCoreRoute) w) := by
    intro M r
    have hCore_w : MeetsContract w p idx.core
        (coreEntryContract ParamConfig.default M r w
          (stepBTimeConst hCoreRoute.C_rt) (hCoreRoute.C_rt + 2000) (hCoreRoute.C_rt + 1000)
          (stepBSpaceConst hCoreRoute.C_sp) hCoreRoute.C_sp) :=
      coreModule_meetsContract_B hHasCore hCoreRouter (fun q hq2 hqr hSub => by
        simpa [stepBModule] using
          (stepBModule hCoreRoute.C_rt hCoreRoute.C_sp).meets bStepB idx.coreOn bCoreRouterEntry
            M r q w p hq2 hqr hHasSB hCoreRouter hSub)
    exact coreAdapterProc_meetsContract hAdapterProc hParams_w hCore_w
  -- 2. Core bridge provides `ProvidesCore` with constant `finalPlayerK`
  have hCoreBridge : ∀ M r,
      ProvidesCore w (finalPlayerK hHierRoute hCoreRoute) M r (coreAdapterCost M r)
        (coreBridgeSpace (finalCoreSpaceConst hCoreRoute) M r) p bBridge := fun M r =>
    providesCore_mono_K (le_max_right _ _) (coreBridgeProcs_providesCore hHasBr (hAdapter_w M r))
  -- 3. Walk-producing router provides `ProvidesRouter` with constant `finalPlayerK`
  have hHierRouter : ProvidesRouter w (finalPlayerK hHierRoute hCoreRoute)
      hHierRoute.route hHierRoute.routeCost hHierRoute.sR p bHierRouterEntry :=
    providesRouter_mono_K (le_max_left _ _) (hHierRoute.meets bHierRouter w p hHasHR)
  -- 4. Level block at `k` meets `ProvidesBuildLevel`
  obtain ⟨hSplit, hTakeLen⟩ := hasAt_split_program (by omega : 0 < levelSeg.length) hHasLvl
  have hLvl_k : ProvidesBuildLevel w
      (buildLevelConst (finalPlayerK hHierRoute hCoreRoute) hHierRoute.C_rt)
      (finalLevelSpace hHierRoute hCoreRoute) p k := by
    have hSplit' : p.procs = p.procs.take k ++
        buildLevelProcs (p.procs.take k).length bHierRouterEntry bBridge ++
        p.procs.drop (k + levelSeg.length) := by
      rw [hTakeLen]; exact hSplit
    have hProv := buildLevelProcs_providesBuildLevel hSplit' hHierRouter hCoreBridge
      hHierRoute.isPlayer hHierRoute.costLe coreAdapterCost_le
    rwa [hTakeLen] at hProv
  -- 5. Wrapper entry at `j` meets `ProvidesBuildLevel` with `+ 20`
  exact buildLevelEntryWrap_providesBuildLevel hj hLvl_k

/-- `finalLevelSpace` satisfies `BuildLevelSpacePoly`. -/
theorem buildFinalLevelSpace_poly
    (hHierRoute : HierRouterModule)
    (hCoreRoute : MultiPairRouterModule) :
    BuildLevelSpacePoly (finalLevelSpace hHierRoute hCoreRoute)
      ((finalCoreSpaceConst hCoreRoute + 1) * 2 ^ 120 +
        (hHierRoute.Cr + 1) * 8 ^ hHierRoute.cr * 2 ^ 14)
      (max 24 (2 * hHierRoute.cr + 4)) :=
  buildLevelSpace_poly_coreBridge hHierRoute.spacePoly

/-- **Main assembly theorem**: `HierPathDSExistsFrom buildTopMinA` from the deterministic
static router alone, with every core, level, static-hierarchy, init-block, delete, query, and
bounds procedure concretely assembled and verified. -/
theorem hierPathDSExistsFrom_of_routers
    (hHierRoute : HierRouterModule)
    (hCoreRoute : MultiPairRouterModule)
    (hCoreRouteNR : ∀ b s, s ∈ hCoreRoute.procs b → s.NoRand) :
    HierPathDSExistsFrom buildTopMinA :=
  hierPathDSExistsFrom_of_level
    (buildFinalLevelProc_noRand hHierRoute hCoreRoute hCoreRouteNR)
    (buildFinalLevelProc_providesBuildLevel hHierRoute hCoreRoute)
    (buildFinalLevelSpace_poly hHierRoute hCoreRoute)

/-- **Chain corollary**: concrete `PathDSImpl` meeting the regimes of the Section 8 chain of the paper from the
deterministic static router alone. -/
theorem exists_pathDS_for_chain_of_routers
    (hDec : Cited.ExpanderDecomposition)
    (hHierRoute : HierRouterModule)
    (hCoreRoute : MultiPairRouterModule)
    (hCoreRouteNR : ∀ b s, s ∈ hCoreRoute.procs b → s.NoRand) :
    ∃ (pathDS : Spanner.PathDSImpl) (C_q : ℝ),
      ConsumerSubpolyAtRegimes pathDS.params.phiOutDen ∧
      ConsumerSubpolyAtRegimes pathDS.params.gExp ∧
      ConsumerSubpolyAtRegimes pathDS.params.gDel ∧
      0 < C_q ∧
      (∀ mMax : ℕ,
        Spanner.capGammaQuery 36 constructExpanderImpl.φ_Const
          (Spanner.pathDSTool_of_impl pathDS) ((decomposeImpl hDec).φ_lb mMax) mMax ≤
          Real.exp (C_q * Real.log (↑mMax + 2) ^ (8 / 9 : ℝ) *
            Real.log (Real.log (↑mMax + 2) + 2) ^ (4 / 3 : ℝ))) ∧
      (∀ mMax : ℕ, (decomposeImpl hDec).decFactor mMax ≤
        1 * Spanner.capGammaL 36 constructExpanderImpl.φ_Const
          (Spanner.pathDSTool_of_impl pathDS) ((decomposeImpl hDec).φ_lb mMax) mMax ^ 2) ∧
      (∀ φ M, 0 < φ →
        (Spanner.pathDSTool_of_impl pathDS).γ_query φ M =
          (Spanner.pathDSTool_of_impl pathDS).γ_ExpPath φ M) ∧
      (∀ b, ∀ s ∈ pathDS.procs b, s.NoRand) :=
  exists_pathDS_for_chain_from hDec
    (hierPathDSExistsFrom_of_routers hHierRoute hCoreRoute hCoreRouteNR)

/-- **Theorem 8.1 (page 39) from the static router alone** (eliminating `hPaths`). -/
theorem theorem_8_1_concrete_of_routers
    (hDec : Cited.ExpanderDecomposition)
    (hHierRoute : HierRouterModule)
    (hCoreRoute : MultiPairRouterModule)
    (hCoreRouteNR : ∀ b s, s ∈ hCoreRoute.procs b → s.NoRand) :
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t : ℝ),
      0 < C_γ ∧
      K_s = 1 + 36 / Real.log 2 ∧
      0 ≤ K_s ∧ 0 ≤ K_t ∧
      (∀ mMax : ℕ,
        (params mMax).K_s = K_s ∧
        (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧
        (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        DynSpanner.SparsifySpec mMax (params mMax) sparsify) :=
  theorem_8_1_concrete_of_hierFrom hDec
    (hierPathDSExistsFrom_of_routers hHierRoute hCoreRoute hCoreRouteNR)

/-- **Theorem 8.1 (page 39) with query time from the static router alone** (eliminating
`hPaths`). -/
theorem theorem_8_1_concrete_with_time_of_routers
    (hDec : Cited.ExpanderDecomposition)
    (hHierRoute : HierRouterModule)
    (hCoreRoute : MultiPairRouterModule)
    (hCoreRouteNR : ∀ b s, s ∈ hCoreRoute.procs b → s.NoRand) :
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t C_q : ℝ),
      0 < C_γ ∧
      K_s = 1 + 36 / Real.log 2 ∧
      0 ≤ K_s ∧ 0 ≤ K_t ∧ 0 < C_q ∧
      (∀ mMax : ℕ,
        (params mMax).K_s = K_s ∧
        (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧
        (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_t ≤ Real.exp (C_q * Real.log ((mMax : ℝ) + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log ((mMax : ℝ) + 2) + 2) ^ (4 / 3 : ℝ)) ∧
        DynSpanner.SparsifySpecWithTime mMax (params mMax) sparsify) :=
  theorem_8_1_concrete_with_time_of_hierFrom hDec
    (hierPathDSExistsFrom_of_routers hHierRoute hCoreRoute hCoreRouteNR)

/-- Concrete walk-producing static router module built from `routerBridgeProcs` and
`routeOrCutPairsProc` (`RouteProgWrap.lean`). -/
noncomputable def hierRouterModule_routeOrCut : HierRouterModule where
  procs := routerBridgeProcs
  entryOff := 0
  noRand := routerBridgeProcs_noRand
  route := routeOrCut
  routeCost := routeOrCutCost
  sR := routerBridgeSpace
  K_rt := routerBridgeK
  C_rt := 20
  Cr := 10000000
  cr := 11
  isPlayer := routeOrCut_isMatchingPlayer
  costLe := routeOrCut_routeCostLe
  spacePoly := fun _ _ _ _ => le_rfl
  meets := fun base w p hAt => by
    simpa using routerBridgeProcs_providesRouter (w := w) hAt

/-- **Assembly from the core router**: `HierPathDSExistsFrom buildTopMinA` parameterized only by
`hCoreRoute` (eliminating `hHierRoute` via `hierRouterModule_routeOrCut`). -/
theorem hierPathDSExistsFrom_of_coreRouter
    (hCoreRoute : MultiPairRouterModule)
    (hCoreRouteNR : ∀ b s, s ∈ hCoreRoute.procs b → s.NoRand) :
    HierPathDSExistsFrom buildTopMinA :=
  hierPathDSExistsFrom_of_routers hierRouterModule_routeOrCut hCoreRoute hCoreRouteNR

private noncomputable def coreRouterModule_routeOrCut : MultiPairRouterModule where
  procs := routerModuleProcs
  entryOff := routerEntryOff
  C_rt := 5000
  C_sp := 200
  meets := fun _ _ _ hp => routeOrCutEntry_meetsContract hp

/-- **Unconditional assembly**: `HierPathDSExistsFrom buildTopMinA` with **no hypotheses**,
instantiating `hHierRoute := hierRouterModule_routeOrCut` and
`hCoreRoute := coreRouterModule_routeOrCut` (`routerModuleProcs`, with `routerModuleProcs_noRand`). -/
theorem hierPathDSExistsFrom : HierPathDSExistsFrom buildTopMinA :=
  hierPathDSExistsFrom_of_routers hierRouterModule_routeOrCut coreRouterModule_routeOrCut
    routerModuleProcs_noRand

private theorem exists_pathDS_cw3_of_level
    {K Cs cs : ℕ} {space : Cited.Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    {PL : HierProc}
    (hPL_nr : PL.NoRand)
    (hPL_spec : ∀ w p j k, PL.At p j k → ProvidesBuildLevel w K space p j)
    (hSpPoly : BuildLevelSpacePoly space Cs cs)
    (a : ℕ) (ha : buildTopMinA ≤ a) :
    ∃ impl : Spanner.PathDSImpl,
      impl.params.phiOutDen = gammaHP a ∧ impl.params.gExp = gammaHP a ∧
      impl.params.gQuery = gammaHP a ∧ impl.params.gDel = (fun _ _ => 1) ∧
      (∀ b, ∀ s ∈ impl.procs b, s.NoRand) ∧ impl.params.cw = 3 := by
  have ha1 : 1 ≤ a := one_le_buildTopMinA.trans ha
  have hS := buildTopStatic_spec hPL_nr hPL_spec hSpPoly a ha
  have hR : RestProcSpec a (restProc (hierInitBuilder a ha1 (initMiddleWriters a)))
      (40000 + 80) (hierBuilderSpace a) 300000 2 :=
    restProc_spec a _ 40000 (hierBuilderSpace a) 300000 2 (hierInitBlockBuilder_spec a ha1)
  have hI := initProc_spec a ha1 (buildTopStaticProc PL)
    (restProc (hierInitBuilder a ha1 (initMiddleWriters a)))
    (2 ^ 20 * (K + 1)) (40000 + 80) 2000 (buildTopStaticSpace K Cs cs a)
    (hierBuilderSpace a) (blockSpace a)
    ((50000 + 2 ^ 15 * (K + 1)) + 5 * Cs * 2000 ^ cs) (max 4 (2 * cs + 2))
    300000 2 2000 2 1 hS hR (blockSpace_form a)
    (fun S G phiNum phiDen M hg => length_initBlock_le S ha1 G phiNum phiDen hg)
    (fun S G phiNum phiDen M hg => length_initBlock_le S ha1 G phiNum phiDen hg)
  have hD := hierDeleteProc_spec a
  have hQ := hierQueryProc_spec a
  obtain ⟨hnrI, hKI, hfI, hspecI⟩ := hI
  obtain ⟨hnrD, hKD, hfD, hspecD⟩ := hD
  obtain ⟨hnrQ, hKQ, hfQ, hspecQ⟩ := hQ
  let PI := initProc (buildTopStaticProc PL) (restProc (hierInitBuilder a ha1 (initMiddleWriters a)))
  let hc := assembleConsts a _ 106496 10000 hKI hKD hKQ _ hierDeleteSpace (hierQuerySpace a)
    _ _ (11 * 16 ^ 12) 12 9 1 1 1 1 hfI hfD hfQ
  have hcw1 : 1 ≤ hc.cw := by simp only [hc, assembleConsts]; omega
  have hcw3 : 3 ≤ hc.cw := by simp only [hc, assembleConsts]; omega
  have hcwEq : hc.cw = 3 := by simp only [hc, assembleConsts]; decide
  let impl : Spanner.PathDSImpl :=
    { params := hc.params
      R := hierRep a
      procs := hierProcs PI hierDeleteProc hierQueryProc
      hprocs_len := fun b => by simp [hierProcs]
      spec := fun w p b hp => by
        obtain ⟨hI', hD', hQ'⟩ := hierProcs_at hp
        refine implements_of_clauses (hierRep_local a)
          (hspecI hc rfl rfl hcw1 w p b _ hI') (fun i => ?_)
        match i with
        | 0 => exact hspecD hc rfl rfl hcw1 w p (b + 1) _ hD'
        | 1 => exact hspecQ hc rfl rfl hcw1 w p (b + 2) _ hQ'
        | i + 2 =>
          intro _ _ _ _ _ _ _ _ _ _ hpre
          exact hpre.elim
      boundsProcs := fun _ => gammaBoundsProcs a
      hbounds_nonempty := fun _ => gammaBoundsProcs_nonempty a
      hbounds_noRand := fun _ => gammaBoundsProcs_noRand a
      boundsSpec := fun w p bB hp =>
        hierParams_boundsSpec a hcw3 (le_refl 1000) (fun _ _ => le_refl 3) w p bB hp }
  refine ⟨impl, rfl, rfl, rfl, rfl, fun b s hs => ?_, hcwEq⟩
  simp only [impl, hierProcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (((rfl | rfl | rfl) | hs) | hs) | hs
  · exact (hnrI _).1
  · exact (hnrD _).1
  · exact (hnrQ _).1
  · exact (hnrI _).2 s hs
  · exact (hnrD _).2 s hs
  · exact (hnrQ _).2 s hs

/-- **Unconditional `PathDSImpl` for Section 8 of the paper** (no `hDec`, no `hPaths`): instantiates
the level-based hierarchy construction with `expanderDecompositionUsed_holds` and the concrete
routers (`hierRouterModule_routeOrCut`, `coreRouterModule_routeOrCut`), also exporting the
word-width multiplier `pathDS.params.cw = 3`. -/
theorem exists_pathDS_for_chain_unconditional :
    ∃ (pathDS : Spanner.PathDSImpl) (C_q : ℝ),
      ConsumerSubpolyAtRegimes pathDS.params.phiOutDen ∧
      ConsumerSubpolyAtRegimes pathDS.params.gExp ∧
      ConsumerSubpolyAtRegimes pathDS.params.gDel ∧
      0 < C_q ∧
      (∀ mMax : ℕ,
        Spanner.capGammaQuery 36 constructExpanderImpl.φ_Const
          (Spanner.pathDSTool_of_impl pathDS)
          ((decomposeImplUsed expanderDecompositionUsed_holds).φ_lb mMax) mMax ≤
          Real.exp (C_q * Real.log (↑mMax + 2) ^ (8 / 9 : ℝ) *
            Real.log (Real.log (↑mMax + 2) + 2) ^ (4 / 3 : ℝ))) ∧
      (∀ mMax : ℕ, (decomposeImplUsed expanderDecompositionUsed_holds).decFactor mMax ≤
        1 * Spanner.capGammaL 36 constructExpanderImpl.φ_Const
          (Spanner.pathDSTool_of_impl pathDS)
          ((decomposeImplUsed expanderDecompositionUsed_holds).φ_lb mMax) mMax ^ 2) ∧
      (∀ φ M, 0 < φ →
        (Spanner.pathDSTool_of_impl pathDS).γ_query φ M =
          (Spanner.pathDSTool_of_impl pathDS).γ_ExpPath φ M) ∧
      (∀ b, ∀ s ∈ pathDS.procs b, s.NoRand) ∧
      pathDS.params.cw = 3 := by
  obtain ⟨a₀, hdec⟩ := decFactor_le_capGammaL_sq_of_gExp_eq expanderDecompositionUsed_holds
  obtain ⟨pathDS, hphi, hexp, hquery, hdel, hnr, hcw⟩ :=
    exists_pathDS_cw3_of_level
      (buildFinalLevelProc_noRand hierRouterModule_routeOrCut coreRouterModule_routeOrCut
        routerModuleProcs_noRand)
      (buildFinalLevelProc_providesBuildLevel hierRouterModule_routeOrCut coreRouterModule_routeOrCut)
      (buildFinalLevelSpace_poly hierRouterModule_routeOrCut coreRouterModule_routeOrCut)
      (max buildTopMinA a₀) (le_max_left buildTopMinA a₀)
  obtain ⟨C_q, hCq, hbd⟩ :=
    capGammaQuery_bound_of_gQuery_eq expanderDecompositionUsed_holds pathDS
      (max buildTopMinA a₀) hquery
  refine ⟨pathDS, C_q, ?_, ?_, ?_, hCq, hbd,
    hdec (max buildTopMinA a₀) (le_max_right buildTopMinA a₀) pathDS hexp,
    fun φ M _ => ?_, hnr, hcw⟩
  · rw [hphi]; exact gammaHP_at_regimes _
  · rw [hexp]; exact gammaHP_at_regimes _
  · rw [hdel]; exact one_at_regimes
  · simp only [Spanner.pathDSTool_of_impl, Spanner.PathDSParams.γ_query,
      Spanner.PathDSParams.γ_ExpPath, hquery, hexp]

/-- **Unconditional Theorem 8.1 (page 39)** (no `hDec`, no `hPaths`): concrete static sparsifier
from `expanderDecompositionUsed_holds` and `hierPathDSExistsFrom`. -/
theorem theorem_8_1_concrete_unconditional :
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t : ℝ),
      0 < C_γ ∧
      K_s = 1 + 36 / Real.log 2 ∧
      0 ≤ K_s ∧ 0 ≤ K_t ∧
      (∀ mMax : ℕ,
        (params mMax).K_s = K_s ∧
        (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧
        (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        DynSpanner.SparsifySpec mMax (params mMax) sparsify) :=
  theorem_8_1_concrete_of_hierFrom_used expanderDecompositionUsed_holds hierPathDSExistsFrom

/-- **Unconditional Theorem 8.1 (page 39) with query time** (no `hDec`, no `hPaths`). -/
theorem theorem_8_1_concrete_with_time_unconditional :
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t C_q : ℝ),
      0 < C_γ ∧
      K_s = 1 + 36 / Real.log 2 ∧
      0 ≤ K_s ∧ 0 ≤ K_t ∧ 0 < C_q ∧
      (∀ mMax : ℕ,
        (params mMax).K_s = K_s ∧
        (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧
        (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_t ≤ Real.exp (C_q * Real.log ((mMax : ℝ) + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log ((mMax : ℝ) + 2) + 2) ^ (4 / 3 : ℝ)) ∧
        DynSpanner.SparsifySpecWithTime mMax (params mMax) sparsify) :=
  theorem_8_1_concrete_with_time_of_hierFrom_used expanderDecompositionUsed_holds hierPathDSExistsFrom

end MinCostFlow.HierPaths

end
