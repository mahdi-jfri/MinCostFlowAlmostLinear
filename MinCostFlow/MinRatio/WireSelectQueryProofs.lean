module

public import MinCostFlow.MinRatio.WireSelectRawProofs
public import MinCostFlow.MinRatio.WireSelectCancelEdges
public import MinCostFlow.MinRatio.WireSelectCancelLoops
import WordRAM.Tactic

/-!
# End-to-end verification of `selectRouteBody` and wired `FindCycle`

Combines the raw cycle selector (`selectRawRoute_runs`, `WireSelectRawProofs.lean`) with the
path-cancellation post-processor (`cancelRoutePaths_runs`, `WireSelectCancelLoops.lean`) to prove:
1. **`ordCycleRouteSelectSpecHeap_proved`**: the fixed program
   `selectRouteBody dMul kOff rawProc cancelProc` (which loads `loc.hb` at runtime from
   `mem[tok.table + dMul * d + kOff]` and reads `emb[eBest]` directly from `embPtr[i]`, with no
   `.const hb` and no sparse-core `opCore 4` readout) meets `OrdCycleRouteSelectSpecHeap`
   (`WireSelectSpec.lean`) for every runtime-allocated `SelectHeapLoc`, with space
   `selectRouteTotalSpace maxPaths L (pathApplySpace L)` and amortized step budget
   `selectRouteTotalCost L maxPaths L (25 * (pathC * (L + 1)^2) * (4 * L + 1))`.
2. **`findCycleStepSpecHeap_proved`**: plugs `ordCycleRouteSelectSpecHeap_proved` into
   `findCycleStepSpecHeap_wired` (`WireSelectSpec.lean`) to verify `ordFindCycleWiredBody`
   end-to-end with the select-heap data structure (`jtree.tex`, Algorithm 1, pages 20–21 & 24;
   Algorithm 2, page 29).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program LinkCut.PathProg

/-- Monotonicity of `selectRawRouteSpace` in the cycle-length bound. -/
private theorem selectRawRouteSpace_mono {K1 K2 : ℕ} (h : K1 ≤ K2) :
    selectRawRouteSpace K1 ≤ selectRawRouteSpace K2 := by
  unfold selectRawRouteSpace; omega

/-- Monotonicity of `selectRawRouteCost` in the cycle-length bound. -/
private theorem selectRawRouteCost_mono {Lk K1 K2 : ℕ} (h : K1 ≤ K2) :
    selectRawRouteCost Lk K1 ≤ selectRawRouteCost Lk K2 := by
  unfold selectRawRouteCost; omega

/-- Monotonicity of `cancelRoutePathsSpace` in the path count `K`. -/
private theorem cancelRoutePathsSpace_mono {K1 K2 L ts : ℕ} (h : K1 ≤ K2) :
    cancelRoutePathsSpace K1 L ts ≤ cancelRoutePathsSpace K2 L ts := by
  unfold cancelRoutePathsSpace
  have hpow : K1 ^ 4 ≤ K2 ^ 4 := Nat.pow_le_pow_left h 4
  have hsq : K1 * K1 ≤ K2 * K2 := Nat.mul_le_mul h h
  exact Nat.mul_le_mul (by omega) (Nat.add_le_add_right (Nat.mul_le_mul_right _ hsq) 1)

/-- Monotonicity of `cancelRoutePathsCost` in the path count `K` and tree budget `tb`. -/
private theorem cancelRoutePathsCost_mono {K1 K2 L tb1 tb2 : ℕ} (hK : K1 ≤ K2) (hB : tb1 ≤ tb2) :
    cancelRoutePathsCost K1 L tb1 ≤ cancelRoutePathsCost K2 L tb2 := by
  unfold cancelRoutePathsCost
  have hpow : K1 ^ 4 ≤ K2 ^ 4 := Nat.pow_le_pow_left hK 4
  have hsq : K1 * K1 ≤ K2 * K2 := Nat.mul_le_mul hK hK
  have hstep : K1 * K1 * (4 * tb1 + 117 * L + 440) ≤ K2 * K2 * (4 * tb2 + 117 * L + 440) :=
    Nat.mul_le_mul hsq (by omega)
  exact Nat.add_le_add_right
    (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hpow) 1)
      (Nat.add_le_add_right hstep 120)) 40

/-- Monotonicity of `cancelRouteEdgesCost` in the edge-list bound. -/
private theorem cancelRouteEdgesCost_mono {K1 K2 : ℕ} (h : K1 ≤ K2) :
    cancelRouteEdgesCost K1 ≤ cancelRouteEdgesCost K2 := by
  unfold cancelRouteEdgesCost
  have hsq : K1 * K1 ≤ K2 * K2 := Nat.mul_le_mul h h
  have h1 : 50 * K1 * K1 ≤ 50 * K2 * K2 := by
    have := Nat.mul_le_mul_left 50 hsq
    simpa only [Nat.mul_assoc] using this
  omega

/-- **`ordCycleRouteSelectSpecHeap_proved`**: the fixed select-heap cycle selector
`selectRouteBody dMul kOff rawProc cancelEdgesProc cancelProc` meets `OrdCycleRouteSelectSpecHeap`
for every runtime-allocated `SelectHeapLoc`, with space
`selectRouteTotalSpace maxPaths L (pathApplySpace L)` and amortized step budget
`selectRouteTotalCost L maxPaths L (25 * (pathC * (L + 1)^2) * (4 * L + 1))`. -/
theorem ordCycleRouteSelectSpecHeap_proved
    {w L P m V psi k epsExp drainUnit dMul kOff
      selectProc rawProc cancelEdgesProc findOppProc cancelProc outerProc innerProc
      isNegProc isZeroProc fillRev splitSteps emitStitches
      initTree cmpExch maxEdges maxPaths : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config}
    {opTree : ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    (hw16 : 16 < 2 ^ w)
    (hdMulW : dMul < 2 ^ w)
    (hfmt4 : fmt.limbBits = 4)
    (hlocalCore : Rcore.Local)
    (hpSel : p.procs[selectProc]? = some (selectRouteBody dMul kOff rawProc cancelEdgesProc cancelProc))
    (hpRaw : p.procs[rawProc]? =
      some (selectRawRouteBody isNegProc isZeroProc fillRev splitSteps emitStitches))
    (hpCancelEd : p.procs[cancelEdgesProc]? =
      some (cancelRouteEdgesLoopBody cancelEdgesProc findOppProc))
    (hpFindOpp : p.procs[findOppProc]? = some (cancelEdgesFindOppBody findOppProc))
    (hpCancel : p.procs[cancelProc]? = some (cancelRoutePathsBody cancelProc outerProc))
    (hpOuter : p.procs[outerProc]? = some (cancelPairOuterBody outerProc innerProc))
    (hpInner : p.procs[innerProc]? = some (cancelPairInnerBody innerProc (opTree 3) cmpExch))
    (hIsNeg : MeetsContract w p isNegProc (Num.isNegativeContract w 4))
    (hIsZero : MeetsContract w p isZeroProc (Num.isZeroContract w 4))
    (hFillRev : ∀ Q : List (ℕ × Bool), MeetsContract w p fillRev (selectFillRevContract w Q))
    (hSplitSteps : ∀ G0 F W fl, MeetsContract w p splitSteps (selectSplitStepsContract w G0 F W fl))
    (hEmitStitches : ∀ G0 W fl p0, MeetsContract w p emitStitches (selectEmitStitchesContract w G0 W fl p0))
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hCmpExch : ∀ ab cd ad cb : ℤ,
      MeetsContract w p cmpExch (pathCompareExchangeContract w 4 ab cd ad cb)) :
    OrdCycleRouteSelectSpecHeap w L P m V psi k epsExp drainUnit dMul kOff
      cfg Rcore p
      selectProc
      (selectRouteTotalSpace maxPaths L (pathApplySpace L))
      (selectRouteTotalCost L maxPaths L
        (25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1)))
      maxEdges maxPaths := by
  refine ⟨selectRouteBody dMul kOff rawProc cancelEdgesProc cancelProc, hpSel, ?_⟩
  intro root descBase workHeap pos size ω mem model tok loc B R G₀ σ σ_mwu γ_ℓ γ_c
    hrep hnum hoff hBd hMod hlogW hmaxE1 hmaxEP hEmbBd hcapE hcapT hLkEq hhbRd hhbLt
    hMatch hMetaE hlocEnd hlocDisj hbelow hwh hz hroom
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  set C := model.chain.toTreeChain
  set F := C.chainTree
  have hRoomUnf : workHeap + (selectRawRouteSpace maxPaths +
      cancelRoutePathsSpace maxPaths L (pathApplySpace L)) < 2 ^ w := hroom
  have hRawSpLe : selectRawRouteSpace maxEdges ≤ selectRawRouteSpace maxPaths :=
    selectRawRouteSpace_mono (by omega)
  have hRawRoom : workHeap + selectRawRouteSpace maxEdges < 2 ^ w := by omega
  -- 1. Run `selectRawRouteBody`
  obtain ⟨work1, cRaw, stRaw, edgesRaw, pathsRaw, hrRaw, hw1Lo, hw1Hi,
      hedMaxRaw, hptMax, heLo, heLtP, heHiRaw, heLenRaw, hpLo, hpHi, hpLen, hEdAt1, hPtAt1,
      hEdOkRaw, hPtOk1, hSame1, hFlow1, hnfEd1, hnfPt1, htag18_1, hrep1, hMatch1, hnum1, hoff1, hBd1,
      hz1, hfr1, hphi1, hcRaw⟩ :=
    selectRawRoute_runs (Rcore := Rcore) (loc := loc) (maxEdges := maxEdges) (maxPaths := maxPaths)
      hw16 hlocalCore hIsNeg hIsZero hFillRev hSplitSteps hEmitStitches
      root descBase workHeap pos size ω mem model tok B R G₀ σ σ_mwu γ_ℓ γ_c
      hrep hnum hoff hBd hMod hmaxE1 hmaxEP hEmbBd hMatch hMetaE hlocEnd hlocDisj hbelow
      hwh hz hRawRoom
  set edgesBase := stRaw.mem (descBase + 2)
  set pathsBase := stRaw.mem (descBase + 4)
  set K := pathsRaw.length
  change workHeap ≤ edgesBase at heLo
  change edgesBase + 2 * edgesRaw.length ≤ pathsBase at heLtP
  change edgesBase + 2 * edgesRaw.length ≤ work1 at heHiRaw
  change workHeap ≤ pathsBase at hpLo
  change pathsBase + 2 * K ≤ work1 at hpHi
  change K ≤ maxPaths at hptMax
  -- Derive forest / edge-weight / vertex-word-bound hypotheses
  have hH := hMod.1
  have hSub := C.forestsAreSubgraphs_of_holds hH
  have hFforest : F.IsForest := C.chainTree_isForest hH hSub
  have hFsub : F.E ⊆ (model.chain.G 0).E := (C.chainTree_isSubgraph hH hSub).2.1
  have hrep0 := hrep
  obtain ⟨hrootDir, _, _, hinitP, hFresh, _, _, _, _, _, _, _, _, _, _, _, _, _, hWire0, htags0⟩ := hrep0
  obtain ⟨hOwn0, t1, t2, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, t20, _⟩ := htags0
  have hℓpos : ∀ e ∈ F.E, 0 < model.extℓ (model.intToExt e) := fun e he =>
    hMod.2.2.2.2.1 _ (hFresh.hRight e (hFsub he)).2
  have h2nW : 2 * model.extG.n + 1 < 2 ^ w := by
    have hdgsz : dynGraphSize model.extG.n tok.rootECap = 4 + 7 * model.extG.n + 9 * tok.rootECap := rfl
    have hlt : tok.rootGraph + (4 + 7 * model.extG.n + 9 * tok.rootECap - 1) < descBase :=
      hbelow _ (Or.inl (hOwn0 _ (by rw [t20 _ (by omega) (by rw [hdgsz]; omega)]; decide)))
    omega
  have hEdRawW : ∀ x ∈ edgesRaw, x.1 < 2 ^ w := by
    intro x hx
    have hxG0 : x.1 ∈ (model.chain.G 0).E := (Finset.mem_sdiff.mp (hEdOkRaw x hx)).1
    have hltCap : x.1 < tok.rootECap := hWire0.2.1.2.2.1 x.1 hxG0
    have hdgsz : dynGraphSize model.extG.n tok.rootECap = 4 + 7 * model.extG.n + 9 * tok.rootECap := rfl
    have hlt : tok.rootGraph + (4 + 7 * model.extG.n + 9 * tok.rootECap - 1) < descBase :=
      hbelow _ (Or.inl (hOwn0 _ (by rw [t20 _ (by omega) (by rw [hdgsz]; omega)]; decide)))
    omega
  -- 1b. Run `cancelRouteEdgesLoopBody` in place on `[edgesBase, edgesBase + 2 * edgesRaw.length)`
  have hAddrEdW : edgesBase + 2 * edgesRaw.length < 2 ^ w := by omega
  obtain ⟨cEd, stEd, edges, hrEd, hedLeRaw, heLenEd, hEdAtEd, hNoOpp, hEdSub, hEdFlow, hFrEd, hcEd⟩ :=
    cancelRouteEdges_runs (maxLen := edgesRaw.length) hw16 hpCancelEd hpFindOpp (by omega) hAddrEdW
      le_rfl heLenRaw hEdAt1 hEdRawW
  have hedMax : edges.length ≤ maxEdges := hedLeRaw.trans hedMaxRaw
  have hEdOk : ∀ x ∈ edges, x.1 ∈ (model.chain.G 0).E \ C.chainTree.E :=
    fun x hx => hEdOkRaw x (hEdSub x hx)
  have hEdAgrLt : ∀ a < descBase, stEd.mem a = stRaw.mem a :=
    fun a ha => hFrEd a (by omega) (Or.inl (by omega))
  have hlocR := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore
  have hlocEd := hlocR root model tok stRaw.mem stEd.mem
    (fun a hf => (hEdAgrLt a (hbelow a hf)).symm)
  have hrep1b : Rrep.rep root model tok stEd.mem := hlocEd.1 hrep1
  have hphi1b : Rrep.phi root tok stEd.mem = Rrep.phi root tok mem := hlocEd.2.symm.trans hphi1
  have hMatch1b : SelectHeapMatchesChain stEd.mem loc 4 P C model.chain.g model.chain.ℓ size :=
    hMatch1.of_agree fun a _ ha => hEdAgrLt a (lt_of_lt_of_le ha hlocEnd)
  have htag1318Ed : ∀ a, (tok.tag a = 13 ∨ tok.tag a = 18) → stEd.mem a = stRaw.mem a := fun a ha =>
    hEdAgrLt a (hbelow a (Or.inl (hOwn0 a (by rcases ha with h | h <;> rw [h] <;> decide))))
  have hoff1b : OffTreeRecInv model L stEd.mem tok.edgeRecords B :=
    offTreeRecInv_of_agree hrep1 hoff1 htag1318Ed
  have hBd1b : OffTreeRecBound model L stEd.mem tok.edgeRecords B :=
    offTreeRecBound_of_agree hrep1 hBd1 htag1318Ed
  have hPtAt1b : PathEndpointsAt stEd.mem pathsBase pathsRaw := fun idx hidx =>
    ⟨(hFrEd _ (by omega) (Or.inr (by omega))).trans (hPtAt1 idx hidx).1,
     (hFrEd _ (by omega) (Or.inr (by omega))).trans (hPtAt1 idx hidx).2⟩
  have hz1b : ZeroFrom stEd.mem work1 := fun a ha =>
    (hFrEd a (by omega) (Or.inr (by omega))).trans (hz1 a ha)
  have hEdDescKeep : ∀ j < 6, j ≠ 3 → stEd.mem (descBase + j) = stRaw.mem (descBase + j) :=
    fun j hj hne => hFrEd (descBase + j) (by omega) (Or.inl (by omega))
  have hbelow1 : ∀ a, Rrep.foot root tok a → a < work1 := fun a hf => by
    have := hbelow a hf; omega
  have hCancelSpLe : cancelRoutePathsSpace K L (pathApplySpace L) ≤
      cancelRoutePathsSpace maxPaths L (pathApplySpace L) :=
    cancelRoutePathsSpace_mono hptMax
  have hCancelRoom : work1 + cancelRoutePathsSpace K L (pathApplySpace L) < 2 ^ w := by omega
  -- 2. Run `cancelRoutePathsBody`
  obtain ⟨work2, cCancel, stCan, tok2, paths, hrCan, hw2Lo, hw2Hi, hlev2, hcap2,
      hrep2, hmetaCan, hMatch2, hnum2, hoff2, hBd2, hPtAt2, hlen2, hPtOk2, hFlowEq, hNoRev,
      htag18_2, hz2, hfr2, hft2, hcCan⟩ :=
    cancelRoutePaths_runs (loc := loc) (descBase := descBase) (maxEdges := maxEdges) (maxPaths := maxPaths)
      hw16 hfmt4 hlocalCore hTreeImpl hCmpExch hpCancel hpOuter hpInner hFforest hFsub hℓpos
      hlogW hmaxE1 hmaxEP hcapE hcapT hlocEnd h2nW
      hrep1b hMatch1b hnum1 hoff1b hBd1b hPtAt1b rfl hPtOk1 hSame1 hnfPt1 hlocDisj htag18_1
      hbelow1 hz1b hpHi (by omega) hCancelRoom
  -- 3. Assemble `Runs` for `selectRouteBody dMul kOff rawProc cancelEdgesProc cancelProc`
  have hHandleRd : mem root = tok.handle := by simpa using hrootDir 0 (by simp)
  have hTableRd : mem (root + 1) = tok.table := by simpa using hrootDir 1 (by simp)
  have hDRd : mem (tok.handle + 11) = cfg.P.d := by
    have h := hinitP 2 (by simp); simpa [Nat.add_assoc] using h
  have hrt1W : root + 1 < 2 ^ w :=
    lt_trans (hbelow _ (Or.inl (hOwn0 _ (by rw [t1 1 (by decide)]; decide)))) (by omega)
  have hhdl11W : tok.handle + 11 < 2 ^ w :=
    lt_trans (hbelow _ (Or.inl (hOwn0 _ (by rw [t2 11 (by decide)]; decide)))) (by omega)
  let s0 := startState [root, descBase, workHeap] mem pos
  let rg7 := Function.update s0.regs 7 tok.handle
  let rg8 := Function.update rg7 8 cfg.P.d
  let rg9 := Function.update rg8 9 tok.table
  let rg10 := Function.update rg9 10 loc.hb
  let rg1 := Function.update rg10 3 work1
  let rg11 := Function.update rg1 11 edgesBase
  let rg12 := Function.update rg11 12 0
  let rg2 := Function.update rg12 4 pathsBase
  let rg3 := Function.update rg2 5 K
  let rg4 := Function.update rg3 6 work2
  have rA7 : Runs w p ω (.assign 7 (.load (.reg 0))) s0 .normal ⟨mem, rg7, pos⟩ 3 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s0, startState, hHandleRd], rfl, rfl, rfl⟩
  have rA8 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 7) (.const 11))))
      ⟨mem, rg7, pos⟩ .normal ⟨mem, rg8, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨cfg.P.d, by
      simp [Expr.eval, BinOp.eval, rg7, show 11 < 2 ^ w by omega, hhdl11W, hDRd], rfl, rfl, rfl⟩
  have rA9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const 1))))
      ⟨mem, rg8, pos⟩ .normal ⟨mem, rg9, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨tok.table, by
      simp [Expr.eval, BinOp.eval, rg8, rg7, s0, startState, show 1 < 2 ^ w by omega, hrt1W, hTableRd],
      rfl, rfl, rfl⟩
  have rA10 : Runs w p ω
      (.assign 10 (.load (.bin .add (.bin .add (.reg 9) (.bin .mul (.const dMul) (.reg 8))) (.const kOff))))
      ⟨mem, rg9, pos⟩ .normal ⟨mem, rg10, pos⟩ 9 :=
    runs_assign_iff.mpr ⟨loc.hb, by
      simp [Expr.eval, BinOp.eval, rg9, rg8, hdMulW, show kOff < 2 ^ w by omega,
        show dMul * cfg.P.d < 2 ^ w by omega,
        show tok.table + dMul * cfg.P.d < 2 ^ w by omega,
        show tok.table + dMul * cfg.P.d + kOff < 2 ^ w by omega, hhbRd],
      rfl, rfl, rfl⟩
  have r1 : Runs w p ω (.call 3 rawProc [.reg 0, .reg 10, .reg 1, .reg 2])
      ⟨mem, rg10, pos⟩ .normal ⟨stRaw.mem, rg1, stRaw.pos⟩ (cRaw + 5) := by
    refine runs_call_iff.mpr ⟨[root, loc.hb, descBase, workHeap], _, .returned work1, stRaw, cRaw,
      ?_, hpRaw, hrRaw, rfl, rfl, ?_⟩
    · simp [evalArgs, Expr.eval, rg10, rg9, rg8, rg7, s0, startState]
    · simp [argsSize, Expr.size]; omega
  have rA11 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 1) (.const 2))))
      ⟨stRaw.mem, rg1, stRaw.pos⟩ .normal ⟨stRaw.mem, rg11, stRaw.pos⟩ 5 :=
    runs_assign_iff.mpr ⟨edgesBase, by
      simp [Expr.eval, BinOp.eval, rg1, rg10, rg9, rg8, rg7, s0, startState, show 2 < 2 ^ w by omega,
        show descBase + 2 < 2 ^ w by omega, edgesBase], rfl, rfl, rfl⟩
  have rCallEd : Runs w p ω (.call 12 cancelEdgesProc [.reg 11, .reg 1, .const 0])
      ⟨stRaw.mem, rg11, stRaw.pos⟩ .normal ⟨stEd.mem, rg12, stEd.pos⟩ (cEd + 4) := by
    refine runs_call_iff.mpr ⟨[edgesBase, descBase, 0], _, .returned 0, stEd, cEd,
      ?_, hpCancelEd, hrEd, rfl, rfl, ?_⟩
    · simp [evalArgs, Expr.eval, rg11, rg1, rg10, rg9, rg8, rg7, s0, startState, show 0 < 2 ^ w by omega]
    · simp [argsSize, Expr.size]; omega
  have r2 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 1) (.const 4))))
      ⟨stEd.mem, rg12, stEd.pos⟩ .normal ⟨stEd.mem, rg2, stEd.pos⟩ 5 :=
    runs_assign_iff.mpr ⟨pathsBase, by
      simp [Expr.eval, BinOp.eval, rg12, rg11, rg1, rg10, rg9, rg8, rg7, s0, startState,
        show 4 < 2 ^ w by omega, show descBase + 4 < 2 ^ w by omega,
        hEdDescKeep 4 (by omega) (by decide), pathsBase], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 1) (.const 5))))
      ⟨stEd.mem, rg2, stEd.pos⟩ .normal ⟨stEd.mem, rg3, stEd.pos⟩ 5 :=
    runs_assign_iff.mpr ⟨K, by
      simp [Expr.eval, BinOp.eval, rg2, rg12, rg11, rg1, rg10, rg9, rg8, rg7, s0, startState,
        show 5 < 2 ^ w by omega, show descBase + 5 < 2 ^ w by omega,
        hEdDescKeep 5 (by omega) (by decide), hpLen, K], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.call 6 cancelProc [.reg 0, .reg 4, .reg 5, .reg 3])
      ⟨stEd.mem, rg3, stEd.pos⟩ .normal ⟨stCan.mem, rg4, stCan.pos⟩ (cCancel + 5) := by
    refine runs_call_iff.mpr ⟨[root, pathsBase, K, work1], _, .returned work2, stCan, cCancel,
      ?_, hpCancel, hrCan, rfl, rfl, ?_⟩
    · simp [evalArgs, Expr.eval, rg3, rg2, rg12, rg11, rg1, rg10, rg9, rg8, rg7, s0, startState]
    · simp [argsSize, Expr.size]; omega
  have r5 : Runs w p ω (.ret (.reg 6))
      ⟨stCan.mem, rg4, stCan.pos⟩ (.returned work2) ⟨stCan.mem, rg4, stCan.pos⟩ 2 :=
    runs_ret_iff.mpr ⟨work2, by simp [Expr.eval, rg4], rfl, rfl, rfl⟩
  have rFull : Runs w p ω (selectRouteBody dMul kOff rawProc cancelEdgesProc cancelProc)
      s0 (.returned work2) ⟨stCan.mem, rg4, stCan.pos⟩
      (3 + (5 + (5 + (9 + ((cRaw + 5) + (5 + ((cEd + 4) + (5 + (5 + ((cCancel + 5) + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) := by
    unfold selectRouteBody
    exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA7,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA8,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA9,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA10,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, rA11,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, rCallEd,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, r4, r5, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- 4. Descriptor words, explicit edges, and `CycleRouteAt` survive `cancelRoutePaths`
  have hDescKeep : ∀ j < 6, stCan.mem (descBase + j) = stEd.mem (descBase + j) := fun j hj =>
    hfr2 (descBase + j) (by omega) (Or.inl (by omega)) fun hf => by
      have := hbelow _ hf; omega
  have hd2 : stCan.mem (descBase + 2) = edgesBase :=
    (hDescKeep 2 (by omega)).trans (hEdDescKeep 2 (by omega) (by decide))
  have hd3 : stCan.mem (descBase + 3) = edges.length := (hDescKeep 3 (by omega)).trans heLenEd
  have hd4 : stCan.mem (descBase + 4) = pathsBase :=
    (hDescKeep 4 (by omega)).trans (hEdDescKeep 4 (by omega) (by decide))
  have hd5 : stCan.mem (descBase + 5) = paths.length := by
    rw [hlen2]; exact (hDescKeep 5 (by omega)).trans ((hEdDescKeep 5 (by omega) (by decide)).trans hpLen)
  have hEdAt2 : ExplicitEdgesAt stCan.mem edgesBase edges := fun idx hidx => by
    have hidx' : idx < edges.length := by simpa using hidx
    have h0 := hEdAtEd idx hidx
    have hA : stCan.mem (edgesBase + 2 * idx) = stEd.mem (edgesBase + 2 * idx) :=
      hfr2 _ (by omega) (Or.inl (by omega)) (hnfEd1 (2 * idx) (by omega))
    have hB : stCan.mem (edgesBase + 2 * idx + 1) = stEd.mem (edgesBase + 2 * idx + 1) :=
      hfr2 _ (by omega) (Or.inl (by omega)) (by rw [Nat.add_assoc]; exact hnfEd1 (2 * idx + 1) (by omega))
    exact ⟨hA.trans h0.1, hB.trans h0.2⟩
  have hRoute : CycleRouteAt model edges paths :=
    cycleRouteAt_of_raw_cancel hEdOk hPtOk2
      (fun ei => by rw [hFlow1 ei, hEdFlow ei, hFlowEq ei]) hNoRev
  -- 5. Combine cost bounds using `Nat.log 2 (2 * extG.n + 1) ≤ 4 * L`
  have hTreeBdLe : pathTreeBudget LinkCut.PathProg.pathC L model.extG.n ≤
      25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) := by
    unfold pathTreeBudget
    exact Nat.mul_le_mul_left _ (by omega)
  have hRawCostLe : selectRawRouteCost loc.Lk maxEdges ≤ selectRawRouteCost L maxPaths := by
    rw [hLkEq]; exact selectRawRouteCost_mono (by omega)
  have hEdCostLe : cancelRouteEdgesCost edgesRaw.length ≤ cancelRouteEdgesCost maxPaths :=
    cancelRouteEdgesCost_mono (by omega)
  have hCanCostLe : cancelRoutePathsCost K L (pathTreeBudget LinkCut.PathProg.pathC L model.extG.n) ≤
      cancelRoutePathsCost maxPaths L (25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1)) :=
    cancelRoutePathsCost_mono hptMax hTreeBdLe
  have hCostTot :
      (3 + (5 + (5 + (9 + ((cRaw + 5) + (5 + ((cEd + 4) + (5 + (5 + ((cCancel + 5) + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
        Rrep.phi root tok2 stCan.mem ≤
      selectRouteTotalCost L maxPaths L
          (25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1)) +
        Rrep.phi root tok mem := by
    unfold selectRouteTotalCost
    dsimp only [Rrep] at hcCan hphi1b ⊢
    change cCancel + (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok2 stCan.mem ≤
      cancelRoutePathsCost K L (pathTreeBudget LinkCut.PathProg.pathC L model.extG.n) +
        (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok stEd.mem at hcCan
    rw [hphi1b] at hcCan
    omega
  refine ⟨work2, _, ⟨stCan.mem, rg4, stCan.pos⟩, tok2, edges, paths, rFull,
    by omega, by unfold selectRouteTotalSpace; change work2 ≤ work1 + cancelRoutePathsSpace K L (pathApplySpace L) at hw2Hi; omega,
    hlev2, hcap2, hedMax, by omega, hNoOpp,
    by rw [hd2]; exact heLo, by rw [hd2]; omega, hd3,
    by rw [hd4]; exact hpLo, by rw [hd4, hlen2]; omega, hd5,
    by rw [hd2]; exact hEdAt2, by rw [hd4]; exact hPtAt2, hRoute,
    fun x hx hf => by rw [hd2] at hf; exact hnfEd1 x (by omega) (hft2 _ hf),
    fun x hx hf => by rw [hd4] at hf; rw [hlen2] at hx; exact hnfPt1 x hx (hft2 _ hf),
    htag18_2, hrep2,
    ((PreservesLevelMeta.refl tok mem).congr_mem_right
      (fun a ht => (hEdAgrLt a (hbelow a (LevelMetaFoot.mem_foot hrep ht))).trans
        (hfr1 a (hbelow a (LevelMetaFoot.mem_foot hrep ht))))).trans hmetaCan,
    hMatch2, hnum2, hoff2, hBd2, hz2,
    fun a ha hnf => (hfr2 a (by omega) (Or.inl (by omega)) hnf).trans ((hEdAgrLt a ha).trans (hfr1 a ha)),
    fun a ha => Or.inl (hft2 a ha),
    hCostTot⟩

/-- **`findCycleStepSpecHeap_proved`**: plugging `ordCycleRouteSelectSpecHeap_proved` into
`findCycleStepSpecHeap_wired` proves that `ordFindCycleWiredBody selectProc evalCycleProc` meets
`FindCycleStepSpecHeap` for a single fixed program independent of runtime heap addresses. -/
theorem findCycleStepSpecHeap_proved
    {w L P m V psi k epsExp drainUnit dMul kOff
      findCycleProc selectProc evalCycleProc rawProc cancelEdgesProc findOppProc cancelProc outerProc innerProc
      isNegProc isZeroProc fillRev splitSteps emitStitches
      initTree cmpExch evalSpace evalBudget maxEdges maxPaths : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config}
    {opTree : ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    (hw16 : 16 < 2 ^ w)
    (hdMulW : dMul < 2 ^ w)
    (hfmt4 : fmt.limbBits = 4)
    (hlocalCore : Rcore.Local)
    (hpFind : p.procs[findCycleProc]? = some (ordFindCycleWiredBody selectProc evalCycleProc))
    (hpSel : p.procs[selectProc]? = some (selectRouteBody dMul kOff rawProc cancelEdgesProc cancelProc))
    (hpRaw : p.procs[rawProc]? =
      some (selectRawRouteBody isNegProc isZeroProc fillRev splitSteps emitStitches))
    (hpCancelEd : p.procs[cancelEdgesProc]? =
      some (cancelRouteEdgesLoopBody cancelEdgesProc findOppProc))
    (hpFindOpp : p.procs[findOppProc]? = some (cancelEdgesFindOppBody findOppProc))
    (hpCancel : p.procs[cancelProc]? = some (cancelRoutePathsBody cancelProc outerProc))
    (hpOuter : p.procs[outerProc]? = some (cancelPairOuterBody outerProc innerProc))
    (hpInner : p.procs[innerProc]? = some (cancelPairInnerBody innerProc (opTree 3) cmpExch))
    (hIsNeg : MeetsContract w p isNegProc (Num.isNegativeContract w 4))
    (hIsZero : MeetsContract w p isZeroProc (Num.isZeroContract w 4))
    (hFillRev : ∀ Q : List (ℕ × Bool), MeetsContract w p fillRev (selectFillRevContract w Q))
    (hSplitSteps : ∀ G0 F W fl, MeetsContract w p splitSteps (selectSplitStepsContract w G0 F W fl))
    (hEmitStitches : ∀ G0 W fl p0, MeetsContract w p emitStitches (selectEmitStitchesContract w G0 W fl p0))
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hCmpExch : ∀ ab cd ad cb : ℤ,
      MeetsContract w p cmpExch (pathCompareExchangeContract w 4 ab cd ad cb))
    (hEval : OrdCycleRouteEvalSpecW w L P m V psi k epsExp drainUnit cfg Rcore p
      evalCycleProc evalSpace evalBudget maxEdges maxPaths) :
    FindCycleStepSpecHeap w L P m V psi k epsExp drainUnit dMul kOff cfg
      Rcore p
      findCycleProc
      (6 + selectRouteTotalSpace maxPaths L (pathApplySpace L) + evalSpace)
      (selectRouteTotalCost L maxPaths L
          (25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1)) + evalBudget + 90)
      maxEdges maxPaths :=
  findCycleStepSpecHeap_wired hlocalCore hpFind
    (ordCycleRouteSelectSpecHeap_proved hw16 hdMulW hfmt4 hlocalCore
      hpSel hpRaw hpCancelEd hpFindOpp hpCancel hpOuter hpInner hIsNeg hIsZero hFillRev hSplitSteps
      hEmitStitches hTreeImpl hCmpExch)
    hEval (by omega)

end MinCostFlow.MinRatio
