module

public import MinCostFlow.MinRatio.UpdateAssembly
public import MinCostFlow.MinRatio.QueryAssembly
public import MinCostFlow.MinRatio.DetectAssembly
public import MinCostFlow.Chain.Ordered.NextFreshBound
public import MinCostFlow.LinkCut.PathProg.Implements
public import MinCostFlow.Num.ModulePlacement
public import MinCostFlow.Num.Sign
import WordRAM.Tactic

/-!
# Bundled deterministic Word-RAM procedure table for `Update`, `Query`, and `Detect`

Packs every concrete Word-RAM helper module and top-level operation body for Definition 4.5
(`minRatioMachineContractWithV` operations `0` = `Update`, `1` = `Query`, `2` = `Detect`) into
one fixed deterministic (`Stmt.NoRand`) relocatable procedure list `solverOpsProcs` of length 183:
- Multiword arithmetic (`copyWords`, `Num.copy`, `add`, `negate`, `subtract`, `multiply`,
  `fixedDivide`, `fixedMultiply`, `loadInt`, `absolute`, `isNegative`, `sign`, `shiftRight`,
  `less`, and `Scaling.Machine.wordPair`).
- Section 6 dynamic path tree (`LinkCut.PathProg.pathTreeBodies 4`).
- Query, Detect, fresh-batch translation, dyadic quality test, path normalization, path tag,
  explicit off-tree edge route update, table growth, shift check, off-tree push, good-cycle
  application, failure output, and shift-cycle loop subroutines.
- Entry points `opUpdate` (`op 0`), `opQuery` (`op 1`), and `opDetect` (`op 2`).

Proves:
- `solverOpsProcs_length`, `solverOpsProcs_noRand`: length 183 and determinism (`NoRand`).
- `solverOpsProcs_meetsAll`: any host program embedding `solverOpsProcs` at `base` (with `14 ≤ w`)
  satisfies every helper contract, `ExplicitRouteUpdateSpec`, and Section 6 `pathTree_implements`.

End-to-end execution lemmas for `op 0`, `op 1`, and `op 2` are in `MinRatioMachineAssembly.lean`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num Scaling.Machine

/-- Fixed entry offsets for every procedure inside `solverOpsProcs`. -/
structure SolverOpsLayout where
  copyWords : ℕ
  copyNum : ℕ
  add : ℕ
  negate : ℕ
  subtract : ℕ
  multiply : ℕ
  fixedDivide : ℕ
  fixedMultiply : ℕ
  loadInt : ℕ
  absolute : ℕ
  isNeg : ℕ
  sign : ℕ
  shiftRight : ℕ
  less : ℕ
  wordPair : ℕ
  pathTree : ℕ
  queryOutput : ℕ
  queryResolved : ℕ
  queryReserved : ℕ
  detectReset : ℕ
  freshInsert : ℕ
  freshDelete : ℕ
  freshRecord : ℕ
  freshScan : ℕ
  freshBatch : ℕ
  qualCompare : ℕ
  qualBody : ℕ
  updateQuality : ℕ
  pathNorm : ℕ
  pathFlowTag : ℕ
  expAddr : ℕ
  expCount : ℕ
  expSignedCount : ℕ
  expAbsent : ℕ
  expFirst : ℕ
  offTreeFlow : ℕ
  offTreeScale : ℕ
  offTreeTag : ℕ
  offTreeCountUpd : ℕ
  expEdgeUpd : ℕ
  expEdgeVisit : ℕ
  expRouteUpd : ℕ
  growTables : ℕ
  shiftCheck : ℕ
  offTreePush : ℕ
  goodNormOut : ℕ
  applyPaths : ℕ
  applyOffTree : ℕ
  goodApply : ℕ
  failOut : ℕ
  cycleLoop : ℕ
  opUpdate : ℕ
  opQuery : ℕ
  opDetect : ℕ

/-- Constant-offset layout matching `solverOpsProcs base`. -/
def solverOpsLayout (base : ℕ) : SolverOpsLayout where
  copyWords := base
  copyNum := base + 1
  add := base + 2
  negate := base + 4
  subtract := base + 6
  multiply := base + 11
  fixedDivide := base + 16
  fixedMultiply := base + 48
  loadInt := base + 59
  absolute := base + 64
  isNeg := base + 69
  sign := base + 70
  shiftRight := base + 73
  less := base + 77
  wordPair := base + 80
  pathTree := base + 81
  queryOutput := base + 145
  queryResolved := base + 146
  queryReserved := base + 147
  detectReset := base + 148
  freshInsert := base + 149
  freshDelete := base + 150
  freshRecord := base + 151
  freshScan := base + 152
  freshBatch := base + 153
  qualCompare := base + 154
  qualBody := base + 155
  updateQuality := base + 156
  pathNorm := base + 157
  pathFlowTag := base + 158
  expAddr := base + 159
  expCount := base + 160
  expSignedCount := base + 161
  expAbsent := base + 162
  expFirst := base + 163
  offTreeFlow := base + 164
  offTreeScale := base + 165
  offTreeTag := base + 166
  offTreeCountUpd := base + 167
  expEdgeUpd := base + 168
  expEdgeVisit := base + 169
  expRouteUpd := base + 170
  growTables := base + 171
  shiftCheck := base + 172
  offTreePush := base + 173
  goodNormOut := base + 174
  applyPaths := base + 175
  applyOffTree := base + 176
  goodApply := base + 177
  failOut := base + 178
  cycleLoop := base + 179
  opUpdate := base + 180
  opQuery := base + 181
  opDetect := base + 182

/-- Operation dispatch function mapping Definition 4.5 opcodes `0, 1, 2` (`Update`, `Query`,
`Detect`) to their fixed procedure indices inside `solverOpsProcs base`. -/
def solverOpsDispatch (base : ℕ) : ℕ → ℕ
  | 0 => base + 180
  | 1 => base + 181
  | 2 => base + 182
  | _ => base

/-- Complete deterministic list of 183 procedure bodies implementing `Update`, `Query`, `Detect`,
and every concrete numeric, path-tree, batch-translation, quality-test, and explicit-edge
subroutine they call, parameterized only by the fixed procedure indices of the three chain-level
subroutines (`chainRefreshProc`, `findCycleProc`, `shiftLevelProc`). -/
def solverOpsProcs (base chainRefreshProc findCycleProc shiftLevelProc : ℕ) : List Stmt :=
  [copyWords] ++
  (Num.copyModule (base + 1) ++
  (Num.addModule (base + 2) 4 ++
  (Num.negateModule (base + 4) 4 ++
  (Num.subtractModule (base + 6) 4 ++
  (Num.multiplyModule (base + 11) 4 ++
  (Num.fixedDivideModule (base + 16) 4 ++
  (Num.fixedMultiplyModule (base + 48) 4 ++
  (Num.loadIntModule (base + 59) 4 ++
  (Num.absoluteModule (base + 64) 4 ++
  (Num.isNegativeModule (base + 69) 4 ++
  (Num.signModule (base + 70) 4 ++
  (Num.shiftRightModule (base + 73) 4 ++
  (Num.lessModule (base + 77) 4 ++
  (Scaling.Machine.wordPairModule ++
  (LinkCut.PathProg.pathTreeBodies 4 (base + 81) ++
  [queryOutputBody (base + 1) (base + 4),
   queryResolvedBody (base + 145),
   queryReservedBody (base + 146) base,
   detectResetBody base (base + 4),
   freshInsertBody,
   freshDeleteBody,
   freshRecordBody (base + 149) (base + 150),
   freshBatchBody (base + 151),
   freshBatchEntry (base + 152),
   updateQualityCompareBody (base + 73) (base + 77),
   updateQualityBody (base + 69) (base + 154),
   updateQualityFromNormBody (base + 6) (base + 155),
   pathNormalizationBody (base + 16) (base + 11),
   pathFlowTagBody (base + 1) (base + 64),
   explicitEdgeAddressBody,
   explicitEdgeCountBody,
   explicitEdgeSignedCountBody (base + 160) (base + 80),
   explicitEdgeAbsentBody (base + 160),
   explicitEdgeFirstBody (base + 162),
   offTreeFlowBody (base + 2) base,
   offTreeScaleBody (base + 59) (base + 48),
   offTreeTagBody (base + 165) (base + 158),
   offTreeCountUpdateBody (base + 166) (base + 164),
   explicitEdgeUpdateBody (base + 161) (base + 167),
   explicitEdgeVisitBody (base + 163) (base + 168),
   explicitEdgeRouteUpdateBody (base + 159) (base + 169),
   growIntTablesBody base,
   shiftCheckBody,
   offTreePushBody (base + 69),
   updateGoodNormOutBody (base + 157) base (base + 158),
   updateGoodApplyPathsBody (base + 81 + 1 + 2),
   updateGoodApplyOffTreeBody (base + 170) (base + 173),
   updateGoodApplyBody (base + 174) (base + 175) (base + 176),
   updateFailOutputBody base,
   updateCycleLoopBody findCycleProc (base + 156) (base + 172) shiftLevelProc,
   solverUpdateBody (base + 171) base (base + 153) chainRefreshProc (base + 179)
     (base + 6) (base + 177) (base + 178),
   solverQueryBody (base + 81 + 1 + 4) (base + 146) (base + 147),
   solverDetectBody (base + 81 + 1 + 6) (base + 81 + 1 + 4) (base + 81 + 1 + 5)
     (base + 69) (base + 148)])))))))))))))))

/-- Numeric budget of the path tree of a solver state. One account bound `B` and one route
bound `R` cover every record of the tree (`PathTreeNumericInv`), fit the machine capacity of
the tree with room for one doubling, and cover the detector threshold of every live edge. This
is what `Detect` needs from the tree (`solverOps_detect_runs`), and it gives the fits that
`Query` needs. -/
def SolverTreeNumericInv {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (P : ℕ) (model : Alg2State cfg)
    (tok : SolverToken cfg L Rcore) : Prop :=
  ∃ B R : ℤ, PathTreeNumericInv tok.tree tok.trees B R ∧
    2 * ((2 * tok.tree.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) ∧
    (∀ e ∈ model.extG.E, |detectorThreshold P cfg.ε (model.extℓ e)| ≤ B) ∧
    (∀ e ∈ model.extG.E, Num.Fits 4 L (-detectorThreshold P cfg.ε (model.extℓ e)))

/-- Final internal-table capacity allocated by wired `Init` so the growth branch of `Update`
never runs on any reached state: `alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * G.m`. -/
def initTargetCap (cfg : Alg2Config) (G : MGraph) : ℕ :=
  Chain.Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * G.m

/-- Extra heap words allocated by wired `Init` beyond `initConcreteSpace` to grow the six
internal tables to `initTargetCap cfg G`. -/
def initWiredExtraSpace (cfg : Alg2Config) (G : MGraph) : ℕ :=
  6 * initTargetCap cfg G

/-- Extra step count of wired `Init` beyond `initConcreteFixed` for overwriting the exact
integer rebuild thresholds and growing the six internal tables to `initTargetCap cfg G`. -/
def initWiredExtraCost (cfg : Alg2Config) (G : MGraph) : ℕ :=
  40 * Nat.clog 2 (4 * cfg.P.M₀ + 2) + 22 * (cfg.P.d + 1) +
    102 * G.m + 17 * initTargetCap cfg G + 450

/-- Modular contract for the solver `Init` procedure against `minRatioInitPreWithV` and
`solverStateRep` (with `drainUnit := detectOffTreeDrainUnit F.limbs`). Matches the
`DSRep.Implements` convention: handle `b = heapArg args`, return value `finalHeap`, and
`Rrep.Respects (fun _ => False) (heapArg args) initSpace mem finalHeap (heapArg args) tok out.mem`.
It also gives `tok.intCap = initTargetCap cfg G` and the numeric budget `SolverTreeNumericInv`
of the new tree. -/
def SolverInitStepSpec {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config) (G : MGraph)
    (m V psi k epsExp : ℕ) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T))
    (p : Program) (initProc : ℕ) (initSpace initBudget : ℕ) : Prop :=
  let L := F.limbs
  let P := F.fmt.precision
  let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
  ∃ body, p.procs[initProc]? = some body ∧
    ∀ (args : List ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      (∀ x ∈ args, x < 2 ^ w) →
      minRatioInitPreWithV F G m V (1 / (2 : ℝ) ^ k) cfg.α args mem →
      ZeroFrom mem (heapArg args) →
      heapArg args + initSpace < 2 ^ w →
      ∃ finalHeap cost out tok,
        Runs w p ω body (startState args mem pos) (.returned finalHeap) out cost ∧
        let s0 := (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).init G
          (readVector mem (args.getD 1 0) F.fmt.limbBits L P m)
          (readVector mem (args.getD 2 0) F.fmt.limbBits L P m)
        MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G
          F.fmt.limbBits L P s0 ∧
        Rrep.rep (heapArg args) s0 tok out.mem ∧
        tok.intCap = initTargetCap cfg G ∧
        SolverTreeNumericInv P s0 tok ∧
        Rrep.Respects (fun _ => False) (heapArg args) initSpace mem finalHeap (heapArg args) tok out.mem ∧
        cost + Rrep.phi (heapArg args) tok out.mem ≤ initBudget

/-- Credit-bearing modular contract for the `Init` procedure, allowing its cost to charge
`toolMul * s0.chain.totalRuntime + treeMul * s0.chain.totalTreeUpdates`. -/
def SolverInitStepSpecCredit {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config) (G : MGraph)
    (m V psi k epsExp : ℕ) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T))
    (p : Program) (initProc : ℕ) (initSpace initFixed toolMul treeMul : ℕ) : Prop :=
  let L := F.limbs
  let P := F.fmt.precision
  let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
  ∃ body, p.procs[initProc]? = some body ∧
    ∀ (args : List ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      (∀ x ∈ args, x < 2 ^ w) →
      minRatioInitPreWithV F G m V (1 / (2 : ℝ) ^ k) cfg.α args mem →
      ZeroFrom mem (heapArg args) →
      heapArg args + initSpace < 2 ^ w →
      ∃ finalHeap cost out tok,
        Runs w p ω body (startState args mem pos) (.returned finalHeap) out cost ∧
        let s0 := (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).init G
          (readVector mem (args.getD 1 0) F.fmt.limbBits L P m)
          (readVector mem (args.getD 2 0) F.fmt.limbBits L P m)
        MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G
          F.fmt.limbBits L P s0 ∧
        Rrep.rep (heapArg args) s0 tok out.mem ∧
        tok.intCap = initTargetCap cfg G ∧
        SolverTreeNumericInv P s0 tok ∧
        Rrep.Respects (fun _ => False) (heapArg args) initSpace mem finalHeap (heapArg args) tok out.mem ∧
        cost + Rrep.phi (heapArg args) tok out.mem ≤
          initFixed + toolMul * s0.chain.totalRuntime + treeMul * s0.chain.totalTreeUpdates

theorem SolverInitStepSpec.toCredit {w : ℕ} {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph}
    {m V psi k epsExp : ℕ} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {p : Program} {initProc initSpace initBudget : ℕ}
    (h : SolverInitStepSpec F cfg G m V psi k epsExp Rcore p initProc initSpace initBudget) :
    SolverInitStepSpecCredit F cfg G m V psi k epsExp Rcore p initProc initSpace initBudget 0 0 := by
  obtain ⟨body, hbody, hrun⟩ := h
  refine ⟨body, hbody, fun args mem pos ω h1 h2 h3 h4 => ?_⟩
  obtain ⟨fh, c, out, tok, hr, hfits, hrep, hcap, hnum, hresp, hc⟩ := hrun args mem pos ω h1 h2 h3 h4
  exact ⟨fh, c, out, tok, hr, hfits, hrep, hcap, hnum, hresp, by simpa using hc⟩

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num Scaling.Machine

theorem solverOpsProcs_length (base chainRefreshProc findCycleProc shiftLevelProc : ℕ) :
    (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc).length = 183 := by
  rfl

open LinkCut.Gen LinkCut.Path LinkCut.PathProg in
private theorem pathCoreBodies_noRand (h b0 : ℕ) :
    ∀ s ∈ pathCoreBodies h b0, s.NoRand := by
  intro s hs
  unfold pathCoreBodies at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [pathInitBody, linkWrap, cutWrap, applyWrap, summaryWrap, readWrap, writeWrap, findWrap,
    copyWords, noteBody, popBody, pickBody, pathRevBody, pathActBody, pathPullBody,
    pathIsIdBody, pathSetIdBody, negBlockBody, addBlockBody, maxIntoBody, segBody,
    pathSumTestBody, pathValTestBody, readValBody, readSumBody, widenBody, writeValBody,
    revNodeBody, applyTagBody, pushDownRevBody, pushDownTagBody, pushDownBody, pullBody,
    rotateBody, splayStepBody, splayLoopBody, pushPathBody, splayBody, detachRightBody,
    attachRightBody, exposeLoopBody, exposeBody, rerootBody, rerootExposeBody, pathApplyBody,
    makeSingletonBody, linkBody, detachRootChildrenBody, cutBody, descendBody, findReadyBody,
    pointReadBody, pointWriteBody, pathActSumTail, pathActTagTail, pathRevTail, childInfo, cutTail, initRecord, forUp, forRange, Stmt.NoRand]

private theorem pathTreeBodies_noRand (h b0 : ℕ) :
    ∀ s ∈ LinkCut.PathProg.pathTreeBodies h b0, s.NoRand := by
  intro s hs
  unfold LinkCut.PathProg.pathTreeBodies at hs
  simp only [List.mem_append] at hs
  rcases hs with hc | hn | ha | hz | hl | he
  · exact pathCoreBodies_noRand h b0 s hc
  · exact Num.negateModule_noRand _ _ s hn
  · exact Num.addModule_noRand _ _ s ha
  · simp only [Num.isZeroModule, List.mem_singleton] at hz; subst hz; exact Num.isZeroBody_noRand _
  · exact Num.lessModule_noRand _ _ s hl
  · exact Num.signExtendModule_noRand _ _ s he

/-- Every procedure body inside `solverOpsProcs` is deterministic (`Stmt.NoRand`). -/
theorem solverOpsProcs_noRand (base chainRefreshProc findCycleProc shiftLevelProc : ℕ) :
    ∀ s ∈ solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc, s.NoRand := by
  intro s hs
  unfold solverOpsProcs at hs
  simp only [List.mem_append] at hs
  rcases hs with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16
  · simp only [List.mem_singleton] at h0; subst h0; simp [copyWords, forRange, forUp, Stmt.NoRand]
  · simp only [Num.copyModule, List.mem_singleton] at h1; subst h1; exact Num.copyBody_noRand
  · exact Num.addModule_noRand _ _ s h2
  · exact Num.negateModule_noRand _ _ s h3
  · exact Num.subtractModule_noRand _ _ s h4
  · exact Num.multiplyModule_noRand _ _ s h5
  · exact Num.fixedDivideModule_noRand _ _ s h6
  · exact Num.fixedMultiplyModule_noRand _ _ s h7
  · exact Num.loadIntModule_noRand _ _ s h8
  · exact Num.absoluteModule_noRand _ _ s h9
  · simp only [Num.isNegativeModule, List.mem_singleton] at h10; subst h10; exact Num.isNegativeBody_noRand 4
  · exact Num.signModule_noRand _ _ s h11
  · exact Num.shiftRightModule_noRand _ _ s h12
  · exact Num.lessModule_noRand _ _ s h13
  · simp only [Scaling.Machine.wordPairModule, List.mem_singleton] at h14; subst h14
    exact Scaling.Machine.wordPairBody_noRand
  · exact pathTreeBodies_noRand 4 _ s h15
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h16
    rcases h16 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact queryOutputBody_noRand _ _
    · simp [queryResolvedBody, Stmt.NoRand]
    · simp [queryReservedBody, Stmt.NoRand]
    · simp [detectResetBody, Stmt.NoRand]
    · simp [freshInsertBody, Stmt.NoRand]
    · simp [freshDeleteBody, Stmt.NoRand]
    · simp [freshRecordBody, Stmt.NoRand]
    · exact freshBatchBody_noRand _
    · exact freshBatchEntry_noRand _
    · simp [updateQualityCompareBody, Stmt.NoRand]
    · simp [updateQualityBody, Stmt.NoRand]
    · simp [updateQualityFromNormBody, Stmt.NoRand]
    · simp [pathNormalizationBody, Stmt.NoRand]
    · exact pathFlowTagBody_noRand _ _
    · exact explicitEdgeAddressBody_noRand
    · exact explicitEdgeCountBody_noRand
    · exact explicitEdgeSignedCountBody_noRand _ _
    · exact explicitEdgeAbsentBody_noRand _
    · exact explicitEdgeFirstBody_noRand _
    · simp [offTreeFlowBody, Stmt.NoRand]
    · exact offTreeScaleBody_noRand _ _
    · exact offTreeTagBody_noRand _ _
    · exact offTreeCountUpdateBody_noRand _ _
    · exact explicitEdgeUpdateBody_noRand _ _
    · exact explicitEdgeVisitBody_noRand _ _
    · exact explicitEdgeRouteUpdateBody_noRand _ _
    · exact growIntTablesBody_noRand _
    · exact shiftCheckBody_noRand
    · exact offTreePushBody_noRand _
    · exact updateGoodNormOutBody_noRand _ _ _
    · exact updateGoodApplyPathsBody_noRand _
    · exact updateGoodApplyOffTreeBody_noRand _ _
    · exact updateGoodApplyBody_noRand _ _ _
    · exact updateFailOutputBody_noRand _
    · exact updateCycleLoopBody_noRand _ _ _ _
    · exact solverUpdateBody_noRand _ _ _ _ _ _ _ _
    · exact solverQueryBody_noRand _ _ _
    · exact solverDetectBody_noRand _ _ _ _ _

private theorem hasAt_peel_ops {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

private theorem hasAt_cons_elem {p : Program} {b : ℕ} {x : Stmt} {xs : List Stmt}
    (h : p.HasAt b (x :: xs)) : p.HasAt b [x] ∧ p.HasAt (b + 1) xs := by
  have h1 : p.HasAt b ([x] ++ xs) := h
  exact ⟨Num.hasAt_append_left h1, Num.hasAt_append_right h1⟩

/-- Any host program embedding `solverOpsProcs` at `base` (with `14 ≤ w`) satisfies every
helper contract, `ExplicitRouteUpdateSpec`, Section 6 `pathTree_implements`, and procedure
placement required by `solverUpdateBody_runs`, `solverQueryBody_runs`, and `solverDetectBody_runs`. -/
theorem solverOpsProcs_meetsAll {w base chainRefreshProc findCycleProc shiftLevelProc : ℕ}
    {p : Program} (hw : 14 ≤ w)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc)) :
    let L := solverOpsLayout base
    MeetsContract w p L.copyWords (copyWordsContract w) ∧
    MeetsContract w p L.subtract (Num.subtractContract w 4) ∧
    MeetsContract w p L.isNeg (Num.isNegativeContract w 4) ∧
    (∀ (fmt : Num.Format w) (limbs : ℕ), fmt.limbBits = 4 →
      (LinkCut.PathProg.pathRep 4 limbs LinkCut.PathProg.pathC).Implements w p
        L.pathTree (fun i => L.pathTree + 1 + i)
        (pathTreeMachineContract fmt limbs LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc limbs))) ∧
    (∀ P val, MeetsContract w p L.queryResolved (queryResolvedContract w 4 P val)) ∧
    (∀ P val, MeetsContract w p L.queryReserved (queryReservedContract w 4 P val)) ∧
    (∀ edge th, MeetsContract w p L.detectReset (detectResetContract w 4 edge th)) ∧
    (∀ r G' H' f' g' next' U',
      MeetsContract w p L.freshBatch (freshBatchEntryContract w r G' H' f' g' next' U')) ∧
    (∀ m U_cap k P inner norm,
      MeetsContract w p L.updateQuality
        (updateQualityFromNormContract w 4 m U_cap k P inner norm)) ∧
    (∀ req mag, MeetsContract w p L.pathNorm (pathNormalizationContract w 4 req mag)) ∧
    (∀ mult, MeetsContract w p L.pathFlowTag (pathFlowTagContract w 4 mult)) ∧
    (∀ limbs, ExplicitRouteUpdateSpec w limbs p L.expRouteUpd) ∧
    p.procs[L.growTables]? = some (growIntTablesBody L.copyWords) ∧
    p.procs[L.shiftCheck]? = some shiftCheckBody ∧
    p.procs[L.offTreePush]? = some (offTreePushBody L.isNeg) ∧
    p.procs[L.goodNormOut]? = some (updateGoodNormOutBody L.pathNorm L.copyWords L.pathFlowTag) ∧
    p.procs[L.applyPaths]? = some (updateGoodApplyPathsBody (L.pathTree + 1 + 2)) ∧
    p.procs[L.applyOffTree]? = some (updateGoodApplyOffTreeBody L.expRouteUpd L.offTreePush) ∧
    p.procs[L.goodApply]? = some (updateGoodApplyBody L.goodNormOut L.applyPaths L.applyOffTree) ∧
    p.procs[L.failOut]? = some (updateFailOutputBody L.copyWords) ∧
    p.procs[L.cycleLoop]? = some (updateCycleLoopBody findCycleProc L.updateQuality L.shiftCheck shiftLevelProc) ∧
    p.procs[L.opUpdate]? = some (solverUpdateBody L.growTables L.copyWords L.freshBatch chainRefreshProc
      L.cycleLoop L.subtract L.goodApply L.failOut) ∧
    p.procs[L.opQuery]? = some (solverQueryBody (L.pathTree + 1 + 4) L.queryResolved L.queryReserved) ∧
    p.procs[L.opDetect]? = some (solverDetectBody (L.pathTree + 1 + 6) (L.pathTree + 1 + 4)
      (L.pathTree + 1 + 5) L.isNeg L.detectReset) := by
  have hw1 : 1 < 2 ^ w := lt_of_lt_of_le (by decide : 1 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw)
  have hbase4 : Num.base 4 < 2 ^ w := by
    change 2 ^ 4 < 2 ^ w; exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hw10 : 2 * 4 + 2 ≤ w := by omega
  have hw14 : 3 * 4 + 2 ≤ w := by omega
  unfold solverOpsProcs at hp
  obtain ⟨hmCopyW, r1⟩ := hasAt_peel_ops (b' := base + 1) hp (by change base + 1 = base + 1; rfl)
  obtain ⟨hmCopyN, r2⟩ := hasAt_peel_ops (b' := base + 2) r1 (by change base + 1 + 1 = base + 2; omega)
  obtain ⟨hmAdd, r3⟩ := hasAt_peel_ops (b' := base + 4) r2 (by change base + 2 + 2 = base + 4; omega)
  obtain ⟨hmNeg, r4⟩ := hasAt_peel_ops (b' := base + 6) r3 (by change base + 4 + 2 = base + 6; omega)
  obtain ⟨hmSub, r5⟩ := hasAt_peel_ops (b' := base + 11) r4 (by change base + 6 + 5 = base + 11; omega)
  obtain ⟨hmMul, r6⟩ := hasAt_peel_ops (b' := base + 16) r5 (by change base + 11 + 5 = base + 16; omega)
  obtain ⟨hmDiv, r7⟩ := hasAt_peel_ops (b' := base + 48) r6 (by change base + 16 + 32 = base + 48; omega)
  obtain ⟨hmFMul, r8⟩ := hasAt_peel_ops (b' := base + 59) r7 (by change base + 48 + 11 = base + 59; omega)
  obtain ⟨hmLoadI, r9⟩ := hasAt_peel_ops (b' := base + 64) r8 (by change base + 59 + 5 = base + 64; omega)
  obtain ⟨hmAbs, r10⟩ := hasAt_peel_ops (b' := base + 69) r9 (by change base + 64 + 5 = base + 69; omega)
  obtain ⟨hmIsNeg, r11⟩ := hasAt_peel_ops (b' := base + 70) r10 (by change base + 69 + 1 = base + 70; omega)
  obtain ⟨hmSign, r12⟩ := hasAt_peel_ops (b' := base + 73) r11 (by change base + 70 + 3 = base + 73; omega)
  obtain ⟨hmShR, r13⟩ := hasAt_peel_ops (b' := base + 77) r12 (by change base + 73 + 4 = base + 77; omega)
  obtain ⟨hmLess, r14⟩ := hasAt_peel_ops (b' := base + 80) r13 (by change base + 77 + 3 = base + 80; omega)
  obtain ⟨hmWP, r15⟩ := hasAt_peel_ops (b' := base + 81) r14 (by change base + 80 + 1 = base + 81; omega)
  obtain ⟨hmTree, rTail⟩ := hasAt_peel_ops (b' := base + 145) r15 (by change base + 81 + 64 = base + 145; omega)
  obtain ⟨hQOut, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hQRes, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hQRsrv, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hDReset, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hFIns, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hFDel, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hFRec, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hFScan, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hFBatch, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hQComp, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hQBody, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hQNorm, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hPNorm, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hPTag, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hEAddr, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hECount, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hESign, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hEAbs, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hEFirst, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hOTFlow, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hOTScale, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hOTTag, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hOTUpd, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hEEUpd, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hEEVis, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hERoute, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hGrow, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hSChk, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hOPush, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hGNorm, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hAPaths, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hAOff, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hGApp, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hFail, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hCLoop, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hOpU, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hOpQ, rTail⟩ := hasAt_cons_elem rTail
  obtain ⟨hOpD, _⟩ := hasAt_cons_elem rTail
  have hcCopyW := copyWords_meetsContract (w := w) hmCopyW
  have hcCopyN := Num.copy_meetsContract (h := 4) hw1 hmCopyN
  have hcAdd := Num.add_meetsContract (by decide) hw10 hmAdd
  have hcNeg := Num.negate_meetsContract hw1 hbase4 hmNeg
  have hcSub := Num.subtract_meetsContract (by decide) hw10 hmSub
  have hcMul := Num.multiply_meetsContract (by decide) hw10 hmMul
  have hcDiv := Num.fixedDivide_meetsContract (by decide) hw14 hmDiv
  have hcFMul := Num.fixedMultiply_meetsContract (by decide) hw10 hmFMul
  have hcLoadI := Num.loadInt_meetsContract hw1 hbase4 hmLoadI
  have hcAbs := Num.absolute_meetsContract (by decide) hw1 hbase4 hmAbs
  have hcIsNeg := Num.isNegative_meetsContract (by decide) hw1 hbase4 hmIsNeg
  have hcSign := Num.sign_meetsContract (by decide) hw1 hbase4 hmSign
  have hcShR := Num.shiftRight_meetsContract (by decide) hw1 hbase4 hmShR
  have hcLess := Num.less_meetsContract (by decide) hw1 hbase4 hmLess
  have hcWP := Scaling.Machine.wordPairStore_meetsContract (w := w) hmWP
  have hcTree : ∀ (fmt : Num.Format w) (limbs : ℕ), fmt.limbBits = 4 →
      (LinkCut.PathProg.pathRep 4 limbs LinkCut.PathProg.pathC).Implements w p
        (base + 81) (fun i => base + 81 + 1 + i)
        (pathTreeMachineContract fmt limbs LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc limbs)) := by
    intro fmt limbs hfmt
    have h := LinkCut.PathProg.pathTree_implements fmt limbs (by omega) (by omega) (hfmt.symm ▸ hmTree)
    simpa only [hfmt] using h
  have hcQRes : ∀ P val, MeetsContract w p (base + 146) (queryResolvedContract w 4 P val) := fun P val =>
    queryResolved_meetsContract val hQRes (queryOutput_meetsContract hQOut hcCopyN hcNeg)
  have hcQRsrv : ∀ P val, MeetsContract w p (base + 147) (queryReservedContract w 4 P val) := fun P val =>
    queryReserved_meetsContract val hQRsrv (hcQRes P val) hcCopyW
  have hcDReset : ∀ edge th, MeetsContract w p (base + 148) (detectResetContract w 4 edge th) := fun edge th =>
    detectReset_meetsContract edge th hDReset hcCopyW hcNeg
  have hcFresh : ∀ r G' H' f' g' next' U',
      MeetsContract w p (base + 153) (freshBatchEntryContract w r G' H' f' g' next' U') :=
    fun r G' H' f' g' next' U' =>
      freshBatchEntry_meetsContract_of_placement r G' H' f' g' next' U' hFBatch hFScan hFRec hFIns hFDel
  have hcQual : ∀ m U_cap k P inner norm,
      MeetsContract w p (base + 156) (updateQualityFromNormContract w 4 m U_cap k P inner norm) :=
    fun m U_cap k P inner norm =>
      updateQualityFromNorm_meetsContract inner norm hQNorm hcSub
        (updateQuality_meetsContract inner norm hQBody hcIsNeg
          (updateQualityCompare_meetsContract inner norm hQComp hcShR hcLess))
  have hcPNorm : ∀ req mag, MeetsContract w p (base + 157) (pathNormalizationContract w 4 req mag) :=
    fun req mag => pathNormalization_meetsContract req mag hPNorm hcDiv hcMul
  have hcPTag : ∀ mult, MeetsContract w p (base + 158) (pathFlowTagContract w 4 mult) :=
    fun mult => pathFlowTag_meetsContract mult hPTag hcCopyN hcAbs
  have hcRoute : ∀ limbs, ExplicitRouteUpdateSpec w limbs p (base + 170) := by
    intro limbs edgesBase edgeRecords dst multPtr edges address old mult ha hroom hname hbelow hdisj hfit
    refine explicitEdgeRouteUpdate_meetsContract edges address old mult ha hroom hname hbelow hdisj hfit
      hERoute (explicitEdgeAddress_meetsContract edges address hEAddr) fun i => ?_
    refine explicitEdgeVisit_meetsContract edges i _ mult hEEVis
      (explicitEdgeFirst_meetsContract edges i hEFirst fun e =>
        explicitEdgeAbsent_meetsContract (edges.take i) e hEAbs
          (fun dir => explicitEdgeCount_meetsContract (edges.take i) e dir hECount))
      fun e => ?_
    exact explicitEdgeUpdate_meetsContract edges e _ mult hEEUpd
      (explicitEdgeSignedCount_meetsContract edges e hESign
        (fun dir => explicitEdgeCount_meetsContract edges e dir hECount) hcWP)
      (offTreeCountUpdate_meetsContract _ mult _ hOTUpd
        (offTreeTag_meetsContract mult _ hOTTag
          (offTreeScale_meetsContract mult _ hOTScale hcLoadI hcFMul) (hcPTag _))
        (offTreeFlow_meetsContract _ _ hOTFlow hcAdd hcCopyW))
  exact ⟨hcCopyW, hcSub, hcIsNeg, hcTree, hcQRes, hcQRsrv, hcDReset, hcFresh, hcQual, hcPNorm,
    hcPTag, hcRoute, hGrow.head, hSChk.head, hOPush.head, hGNorm.head, hAPaths.head, hAOff.head,
    hGApp.head, hFail.head, hCLoop.head, hOpU.head, hOpQ.head, hOpD.head⟩

end MinCostFlow.MinRatio
