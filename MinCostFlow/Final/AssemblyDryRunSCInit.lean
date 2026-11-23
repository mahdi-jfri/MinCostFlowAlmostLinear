module

public import MinCostFlow.Final.AssemblyDryRun
public import MinCostFlow.Final.AssemblyDryRunSCStretch
public import MinCostFlow.MinRatio.WireInitConcrete
public import MinCostFlow.MinRatio.PathSlotBind
public import MinCostFlow.DynSpanner.Program.DynGraphInit
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.LastLevelProgram.RepresentativeGraph
import Mathlib.Tactic

/-!
# Proved concrete initializer module for the dry run (`AssemblyDryRunSCInit`)

Installs the concrete deterministic initializer `initConcreteBody` (`MinRatio/WireInitConcrete.lean`)
together with its local deterministic helper procedures (`buildSortedEndsBody`, `wireCoreLenBody`,
`wireCoreLenEdgeBody`, `pathSlotBindBody`, and `dgOpsProcs`–`dgBatchProcs`) into the inner-level
code block of `solverTail`, while keeping the other inner procedures (`paramSetup`,
`ordChainCore`, `selectRoute`, `evalCycle`, `shiftTermChain`, `shiftDeepChain`) parameterized by
`SolverInnerOpen`.

Provides:
* `dryInitConcreteProcs`, `dryInitConcreteProcs_length`, `dryInitConcreteProcs_noRand`, and
  `SolverInnerOpen.toInnerCode` (`toInnerCode_isDeterministic`, `toInnerCode_initConcrete`);
* `solverOpsProcs_initHelpers`: extracts `copyWords`, `negate`, `multiply`, `fixedDivide`,
  `signExtend`, `shiftLeft`, `integerDivide`, and `pathTreeBodies 4` directly from `solverOpsProcs`;
* `packedLastLevelBodies_readout_at`: proves `p.procs[b + 16]? = some LastLevelProgram.readoutBody`
  for the relocated last-level bodies;
* `sparseCoreBundleRestartToolMachWith_initOrdEqOnE` and `fixedPointLastLevelTool_buildEqOnE`;
* `ordInitConcreteSpecW_mono`: monotonicity of `OrdInitConcreteSpecW` in `initSpace'`, `initFixed`,
  and `initMul`;
* `dryInitConcrete_meets_spec`: applies `initConcreteBody_meets_spec` inside `dryLinkedProgram`,
  discharging all 22 concrete code, format, numeric, graph, and word-size hypotheses automatically
  and leaving only the explicit bridge hypotheses (`paramSetup`, `hCoreImpl`, `hLastImpl`,
  `hLastSpaceLe`, `hInitSpaceLe`, `hCoreLenFits`, `hLastStretchFits`, and size bounds on `sz`).
  The sparse core meets `sparseCoreOrdMachineContractKFBL` at the caps `(n, m)` of the input
  graph, which fit under the cap limit (`dry_inputCaps_le_capLimit`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio LastLevelProgram DynSpanner.Program

/-! ## Concrete Init module and the other inner-level code -/

/-- The other inner-level procedures, given as parameters, once the concrete initializer
`initConcreteBody` and its local deterministic helpers are installed: the five chain/cycle/shift entries
plus the parameter-setup procedure (`initParamSetupContract`). -/
structure SolverInnerOpen where
  procs : SolverInnerEnv → List Stmt
  paramSetupOff : ℕ
  ordChainCoreOff : ℕ
  selectRouteOff : ℕ
  evalCycleOff : ℕ
  shiftTermChainOff : ℕ
  shiftDeepChainOff : ℕ

/-- Determinism of the inner-level procedures given as parameters. -/
def SolverInnerOpen.IsDeterministic (openInner : SolverInnerOpen) : Prop :=
  ∀ env, ∀ s ∈ openInner.procs env, s.NoRand

/-- Fixed length of `dryInitConcreteProcs`: `initConcreteBody`, `buildSortedEndsBody`,
`wireCoreLenBody`, `wireCoreLenEdgeBody`, `pathSlotBindBody`, and the 15 dynamic-graph
initialization procedures (`dgOpsProcs`, `dgEdgeProcs`, `dgSplitProcs`, `dgBatchProcs`). -/
def dryInitConcreteLen : ℕ := 20

/-- Concrete deterministic procedure block of length `20` placed at `env.innerBase`, implementing
`initConcreteBody` (at offset `0`) and its local helpers, reusing `solverOpsProcs` at `env.opsBase`
for multiword arithmetic (`copyWords`, `negate`, `multiply`, `fixedDivide`, `signExtend`,
`shiftLeft`, `integerDivide`) and the Section 6 path tree (`pathTreeBodies 4 (env.opsBase + 81)`). -/
def dryInitConcreteProcs (env : SolverInnerEnv) (paramSetupProc : ℕ) : List Stmt :=
  let b := env.innerBase
  let ops := env.opsBase
  [initConcreteBody (b + 17 + dgIdxInitFromLists) paramSetupProc (b + 1)
      env.scInit (env.scOp 3) (env.scOp 2) (b + 2) (env.scOp 5)
      env.lastInit (env.lastOp 0) (ops + 81) (ops + 81 + 1)
      (b + 4) (ops + 20) (ops + 16) (ops + 4) ops,
   buildSortedEndsBody,
   wireCoreLenBody (b + 3),
   wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops,
   pathSlotBindBody] ++
  (dgOpsProcs ++
  (dgEdgeProcs (b + 5) ++
  (dgSplitProcs (b + 5) (b + 14) ++
   dgBatchProcs (b + 5) (b + 12) (b + 14) (b + 17))))

/-- Assemble a `SolverInnerCode` from `dryInitConcreteProcs` (at `env.innerBase`) followed by the
other procedures `openInner` (at `env.innerBase + 20`). -/
def SolverInnerOpen.toInnerCode (openInner : SolverInnerOpen) : SolverInnerCode where
  procs env :=
    dryInitConcreteProcs env (env.innerBase + dryInitConcreteLen + openInner.paramSetupOff) ++
      openInner.procs { env with innerBase := env.innerBase + dryInitConcreteLen }
  initConcreteOff := 0
  ordChainCoreOff := dryInitConcreteLen + openInner.ordChainCoreOff
  selectRouteOff := dryInitConcreteLen + openInner.selectRouteOff
  evalCycleOff := dryInitConcreteLen + openInner.evalCycleOff
  shiftTermChainOff := dryInitConcreteLen + openInner.shiftTermChainOff
  shiftDeepChainOff := dryInitConcreteLen + openInner.shiftDeepChainOff

/-- Absolute procedure index of `paramSetup` inside the linked dry-run program for
`openInner.toInnerCode`. -/
def dryParamSetupProc (sc : SparseCoreCode) (openInner : SolverInnerOpen) : ℕ :=
  (dryTailLay sc openInner.toInnerCode).innerBase + dryInitConcreteLen + openInner.paramSetupOff

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio LastLevelProgram DynSpanner.Program

private theorem hasAt_peel_init {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

/-! ## Length, determinism, and placement of `dryInitConcreteProcs` -/

theorem dryInitConcreteProcs_length (env : SolverInnerEnv) (paramSetupProc : ℕ) :
    (dryInitConcreteProcs env paramSetupProc).length = dryInitConcreteLen := by
  rfl

theorem dryInitConcreteProcs_noRand (env : SolverInnerEnv) (paramSetupProc : ℕ) :
    ∀ s ∈ dryInitConcreteProcs env paramSetupProc, s.NoRand := by
  intro s hs
  unfold dryInitConcreteProcs at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (rfl | rfl | rfl | rfl | rfl) | h1 | h2 | h3 | h4
  · exact initConcreteBody_noRand _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact buildSortedEndsBody_noRand
  · exact wireCoreLenBody_noRand _
  · exact wireCoreLenEdgeBody_noRand _ _ _ _
  · simp [pathSlotBindBody, Stmt.NoRand]
  · exact dgOpsProcs_noRand s h1
  · exact dgEdgeProcs_noRand _ s h2
  · exact dgSplitProcs_noRand _ _ s h3
  · exact dgBatchProcs_noRand _ _ _ _ s h4

theorem SolverInnerOpen.toInnerCode_isDeterministic {openInner : SolverInnerOpen}
    (hdet : openInner.IsDeterministic) : openInner.toInnerCode.IsDeterministic := by
  intro env s hs
  rcases List.mem_append.mp hs with h | h
  · exact dryInitConcreteProcs_noRand _ _ s h
  · exact hdet _ s h

/-- Extract every local procedure placement and helper contract from `dryInitConcreteProcs`. -/
theorem dryInitConcreteProcs_hasAt {w : ℕ} {p : Program} {env : SolverInnerEnv}
    {paramSetupProc : ℕ}
    (hp : p.HasAt env.innerBase (dryInitConcreteProcs env paramSetupProc)) :
    let b := env.innerBase
    let ops := env.opsBase
    p.procs[b]? = some (initConcreteBody (b + 17 + dgIdxInitFromLists) paramSetupProc (b + 1)
        env.scInit (env.scOp 3) (env.scOp 2) (b + 2) (env.scOp 5)
        env.lastInit (env.lastOp 0) (ops + 81) (ops + 81 + 1)
        (b + 4) (ops + 20) (ops + 16) (ops + 4) ops) ∧
    p.procs[b + 1]? = some buildSortedEndsBody ∧
    p.procs[b + 2]? = some (wireCoreLenBody (b + 3)) ∧
    p.procs[b + 3]? = some (wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops) ∧
    MeetsContract w p (b + 4) (pathSlotBindContract w) ∧
    ∀ vCap eCap G vL eEdges,
      MeetsContract w p (b + 17 + dgIdxInitFromLists)
        (dgInitFromListsContract w vCap eCap G vL eEdges) := by
  dsimp only
  unfold dryInitConcreteProcs at hp
  obtain ⟨hHead, hDg⟩ := hasAt_peel_init (b' := env.innerBase + 5) hp (by change _ + 5 = _; rfl)
  obtain ⟨hOps, hRest1⟩ := hasAt_peel_init (b' := env.innerBase + 12) hDg
    (by change env.innerBase + 5 + 7 = env.innerBase + 12; omega)
  obtain ⟨hEdge, hRest2⟩ := hasAt_peel_init (b' := env.innerBase + 14) hRest1
    (by change env.innerBase + 12 + 2 = env.innerBase + 14; omega)
  obtain ⟨hSplit, hBatch⟩ := hasAt_peel_init (b' := env.innerBase + 17) hRest2
    (by change env.innerBase + 14 + 3 = env.innerBase + 17; omega)
  have h0 : p.procs[env.innerBase]? = some _ := hHead.head
  have h1 : p.procs[env.innerBase + 1]? = some buildSortedEndsBody :=
    hHead.get (i := 1) (by simp)
  have h2 : p.procs[env.innerBase + 2]? = some (wireCoreLenBody (env.innerBase + 3)) :=
    hHead.get (i := 2) (by simp)
  have h3 : p.procs[env.innerBase + 3]? =
      some (wireCoreLenEdgeBody (env.opsBase + 17) (env.opsBase + 11) (env.opsBase + 22) env.opsBase) :=
    hHead.get (i := 3) (by simp)
  have h4at : p.HasAt (env.innerBase + 4) [pathSlotBindBody] := by
    intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simpa using hHead.get (i := 4) (by simp)
  exact ⟨h0, h1, h2, h3, pathSlotBind_meetsContract h4at,
    fun vCap eCap G vL eEdges => dgInitFromLists_meetsContract hBatch hEdge hOps⟩

/-! ## Extracting Init numeric/tree helpers from `solverOpsProcs` and readout from last-level -/

/-- Extract the arithmetic contracts (`copyWords`, `negate`, `multiply`, `fixedDivide`,
`signExtend`, `shiftLeft`, `integerDivide`) and the Section 6 path-tree placement directly from
`solverOpsProcs` at `base` (for `14 ≤ w`). -/
theorem solverOpsProcs_initHelpers {w base chainRefreshProc findCycleProc shiftLevelProc : ℕ}
    {p : Program} (hw : 14 ≤ w)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc)) :
    MeetsContract w p base (copyWordsContract w) ∧
    MeetsContract w p (base + 4) (Num.negateContract w 4) ∧
    MeetsContract w p (base + 11) (Num.multiplyContract w 4) ∧
    MeetsContract w p (base + 16) (Num.fixedDivideContract w 4) ∧
    MeetsContract w p (base + 17) (Num.signExtendContract w 4) ∧
    MeetsContract w p (base + 20) (Num.shiftLeftContract w 4) ∧
    MeetsContract w p (base + 22) (Num.integerDivideContract w 4) ∧
    p.HasAt (base + 81) (LinkCut.PathProg.pathTreeBodies 4 (base + 81)) := by
  have hw1 : 1 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 1 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw)
  have hbase4 : Num.base 4 < 2 ^ w := by
    change 2 ^ 4 < 2 ^ w; exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hw10 : 2 * 4 + 2 ≤ w := by omega
  have hw14 : 3 * 4 + 2 ≤ w := by omega
  unfold solverOpsProcs at hp
  obtain ⟨hmCopyW, r1⟩ := hasAt_peel_init (b' := base + 1) hp (by change base + 1 = base + 1; rfl)
  obtain ⟨_, r2⟩ := hasAt_peel_init (b' := base + 2) r1 (by change base + 1 + 1 = base + 2; omega)
  obtain ⟨_, r3⟩ := hasAt_peel_init (b' := base + 4) r2 (by change base + 2 + 2 = base + 4; omega)
  obtain ⟨hmNeg, r4⟩ := hasAt_peel_init (b' := base + 6) r3 (by change base + 4 + 2 = base + 6; omega)
  obtain ⟨_, r5⟩ := hasAt_peel_init (b' := base + 11) r4 (by change base + 6 + 5 = base + 11; omega)
  obtain ⟨hmMul, r6⟩ := hasAt_peel_init (b' := base + 16) r5 (by change base + 11 + 5 = base + 16; omega)
  obtain ⟨hmFDiv, r7⟩ := hasAt_peel_init (b' := base + 48) r6 (by change base + 16 + 32 = base + 48; omega)
  obtain ⟨_, r8⟩ := hasAt_peel_init (b' := base + 59) r7 (by change base + 48 + 11 = base + 59; omega)
  obtain ⟨_, r9⟩ := hasAt_peel_init (b' := base + 64) r8 (by change base + 59 + 5 = base + 64; omega)
  obtain ⟨_, r10⟩ := hasAt_peel_init (b' := base + 69) r9 (by change base + 64 + 5 = base + 69; omega)
  obtain ⟨_, r11⟩ := hasAt_peel_init (b' := base + 70) r10 (by change base + 69 + 1 = base + 70; omega)
  obtain ⟨_, r12⟩ := hasAt_peel_init (b' := base + 73) r11 (by change base + 70 + 3 = base + 73; omega)
  obtain ⟨_, r13⟩ := hasAt_peel_init (b' := base + 77) r12 (by change base + 73 + 4 = base + 77; omega)
  obtain ⟨_, r14⟩ := hasAt_peel_init (b' := base + 80) r13 (by change base + 77 + 3 = base + 80; omega)
  obtain ⟨_, r15⟩ := hasAt_peel_init (b' := base + 81) r14 (by change base + 80 + 1 = base + 81; omega)
  obtain ⟨hmTree, _⟩ := hasAt_peel_init (b' := base + 145) r15 (by change base + 81 + 64 = base + 145; omega)
  -- Peel `signExtendModule`, `shiftLeftModule`, and `integerDivideModule` out of `fixedDivideModule`
  have hmFDiv' := hmFDiv
  unfold Num.fixedDivideModule at hmFDiv'
  obtain ⟨_, fd1⟩ := hasAt_peel_init (b' := base + 17) hmFDiv' (by change base + 16 + 1 = base + 17; omega)
  obtain ⟨hmSignExt, fd2⟩ := hasAt_peel_init (b' := base + 20) fd1 (by change base + 17 + 3 = base + 20; omega)
  obtain ⟨hmShiftL, fd3⟩ := hasAt_peel_init (b' := base + 22) fd2 (by change base + 20 + 2 = base + 22; omega)
  obtain ⟨hmIntDiv, _⟩ := hasAt_peel_init (b' := base + 47) fd3 (by change base + 22 + 25 = base + 47; omega)
  exact ⟨copyWords_meetsContract hmCopyW,
    Num.negate_meetsContract hw1 hbase4 hmNeg,
    Num.multiply_meetsContract (by decide) hw10 hmMul,
    Num.fixedDivide_meetsContract (by decide) hw14 hmFDiv,
    Num.signExtend_meetsContract (by decide) hw1 hbase4 hmSignExt,
    Num.shiftLeft_meetsContract (by decide) hw10 hmShiftL,
    Num.integerDivide_meetsContract (by decide) hw14 hmIntDiv,
    hmTree⟩

/-- The relocated last-level bodies place `LastLevelProgram.readoutBody` verbatim at `b + 16`
(since `readoutBody` contains no `.call` statements). -/
theorem packedLastLevelBodies_readout_at {guest : Program} {d c b : ℕ} {p : Program}
    (hp : p.HasAt b (packedLastLevelBodies guest d c b)) :
    p.procs[b + 16]? = some LastLevelProgram.readoutBody := by
  have h16 := (packedLastLevelProgram_entries guest d c).2.2.1
  have hlen : 16 < (packedLastLevelProgram guest d c).procs.length := by
    by_contra h
    have hnone : (packedLastLevelProgram guest d c).procs[16]? = none :=
      List.getElem?_eq_none (by omega)
    rw [hnone] at h16
    cases h16
  have hget := hp 16 (by simpa [packedLastLevelBodies, shiftProgramProcs] using hlen)
  have hval : (packedLastLevelProgram guest d c).procs[16] = LastLevelProgram.readoutBody := by
    have h1 := List.getElem?_eq_getElem hlen
    rw [h1] at h16
    exact Option.some.inj h16
  simpa [packedLastLevelBodies, shiftProgramProcs, hval, shiftProcIds, readoutBody] using hget

/-! ## Tool extensionality and `OrdInitConcreteSpecW` monotonicity -/

/-- `sparseCoreBundleRestartToolMachWith` depends only on edge lengths on `G.E` and ignores the
gradient argument, for every `lsfInit`. -/
theorem sparseCoreBundleRestartToolMachWith_initOrdEqOnE
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (params : ℕ → DynSpanner.SparsifyParams) (spanConst : ℕ) :
    ToolInitOrdEqOnE (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst) := by
  intro k M N G len len' grad grad' ord h
  have htr : (fun j => initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G len ord j) =
      (fun j => initBundleTreeWithParams lsfInit L sparsify params spanConst k M N G len' ord j) := by
    funext j
    have hsafe := SparseCore.safeLen_eq_of_eq_on_E h
    have hcs := initCompLSFWith_eq_of_eq_on_E lsfInit G h k j
    unfold initBundleTreeWithParams
    simp only [hcs, hsafe]
  dsimp only [sparseCoreBundleRestartToolMachWith, initBundleCoreWithParams]
  rw [htr]

/-- `fixedPointLastLevelTool` depends only on edge lengths on `G.E` (for any graph `G`). -/
theorem fixedPointLastLevelTool_buildEqOnE
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) :
    LastLevelBuildEqOnE (LastLevelProgram.fixedPointLastLevelTool oracle C) := by
  classical
  intro G len len' hlen
  have hn (e : ℕ) (he : e ∈ nonLoopEdges G) : len e = len' e :=
    hlen e ((Finset.mem_filter.mp he).1)
  have hshort (e : ℕ) (he : e ∈ nonLoopEdges G) :
      shortestEdge G len (edgePairKey G e) = shortestEdge G len' (edgePairKey G e) := by
    obtain ⟨hf, hkey, _⟩ := shortestEdge_spec (ℓ := len) he
    conv_rhs => rw [← hkey]
    apply eq_shortestEdge_of_minimal hf
    intro g hg hgkey
    have hkey' : edgePairKey G g = edgePairKey G e := hgkey.trans hkey
    obtain ⟨_, _, hmin⟩ := shortestEdge_spec (ℓ := len) hg
    rw [hkey'] at hmin
    rw [← hn _ hf, ← hn _ hg]
    exact hmin.elim (fun h => ⟨h.le, fun heq => (h.ne heq).elim⟩)
      (fun h => ⟨h.1.le, fun _ => h.2⟩)
  have hrep : representativeGraph G len = representativeGraph G len' := by
    unfold representativeGraph
    have he : ((nonLoopEdges G).image (edgePairKey G)).image (shortestEdge G len) =
        ((nonLoopEdges G).image (edgePairKey G)).image (shortestEdge G len') := by
      apply Finset.image_congr
      intro k hk
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hk
      exact hshort e he
    rw [he]
  have hsafe : LSF.safeLen (representativeGraph G len') len =
      LSF.safeLen (representativeGraph G len') len' := by
    funext e
    by_cases he : e ∈ (representativeGraph G len').E
    · rw [LSF.safeLen_eq_of_mem len he, LSF.safeLen_eq_of_mem len' he]
      exact hlen e ((Finset.mem_filter.mp (representative_mem he).1).1)
    · simp [LSF.safeLen, he]
  have hquery (P : ℕ) :
      stretchQuery oracle (representativeGraph G len') len P =
        stretchQuery oracle (representativeGraph G len') len' P := by
    unfold stretchQuery; rw [hsafe]
  change (fixedPointLastLevelTool oracle C).build G len = _
  simp only [fixedPointLastLevelTool]
  split
  · rw [hrep]
    simp only [hquery, hsafe]
    congr 1; funext j; congr 1; funext e
    split
    · rename_i he; rw [hshort e he]
    · rfl
  · rfl

/-- Monotonicity of `OrdInitConcreteSpecW` in `initSpace'`, `initFixed`, and `initMul`. -/
theorem ordInitConcreteSpecW_mono
    {w L P E m V psi k epsExp capExp limbMul capLimit wordExp
      initSpace₁ initSpace₂ initFixed₁ initFixed₂ initMul₁ initMul₂ initConcreteProc : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {G : MGraph} {p : Program}
    {B_tree : ℤ}
    (h : OrdInitConcreteSpecW w L P E m V psi k epsExp cfg Rcore G p initConcreteProc B_tree
      capExp limbMul capLimit wordExp initSpace₁ initFixed₁ initMul₁)
    (hsp : initSpace₁ ≤ initSpace₂) (hfix : initFixed₁ ≤ initFixed₂)
    (hmul : initMul₁ ≤ initMul₂) :
    OrdInitConcreteSpecW w L P E m V psi k epsExp cfg Rcore G p initConcreteProc B_tree
      capExp limbMul capLimit wordExp initSpace₂ initFixed₂ initMul₂ := by
  obtain ⟨body, hbody, hrun⟩ := h
  refine ⟨body, hbody, fun graph gradient lengths root pos ω mem hroom hWord hCap hG hg hl hgr hv hLW hGR hz => ?_⟩
  obtain ⟨mid, cInit, rootGraph, table, levelsEnd, treeEnd, finalHeap, vcLast, ecLast,
    sFin, yTree, slotFin, nameFin, yCore, yTerm,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28⟩ :=
    hrun graph gradient lengths root pos ω mem (by omega) hWord hCap hG hg hl hgr hv hLW hGR hz
  refine ⟨mid, cInit, rootGraph, table, levelsEnd, treeEnd, finalHeap, vcLast, ecLast,
    sFin, yTree, slotFin, nameFin, yCore, yTerm,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, le_trans h27 (Nat.add_le_add_left hsp root), ?_⟩
  have hmul' := Nat.mul_le_mul_right
    (Chain.Ordered.algorithm2_init cfg G
      (IPM.Machine.readVector mem gradient 4 L P m)
      (IPM.Machine.readVector mem lengths 4 L P m)).chain.totalRuntime hmul
  omega

/-! ## Discharging `OrdInitConcreteSpecW` in the dry run via `initConcreteBody_meets_spec` -/

/-- Precision and epsilon-exponent arithmetic for `ipmQualityMinRatioFormat`. -/
private theorem dry_ipmQuality_arith (m V k : ℕ) :
    let L := ipmQualityLimbs m V k
    let P := ipmQualityPrecision m V k
    let epsExp := k + Num.IPM.alphaExponent m V + 10
    P ≤ 4 * L ∧ 4 ∣ P ∧ 0 < L ∧ epsExp ≤ P ∧ P - epsExp + 1 < 4 * L := by
  have hk : k ≤ qualitySlackExponent m V k := qualityExponent_le_qualitySlackExponent m V k
  have hα : Num.IPM.alphaExponent m V ≤ Num.IPM.alphaScale m V := by
    unfold Num.IPM.alphaExponent Num.IPM.alphaScale
    have hc : Nat.clog 2 (1000 * (m.size + V.size)) ≤ 1000 * (m.size + V.size) :=
      (Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self.le
    omega
  dsimp only [ipmQualityLimbs, ipmQualityPrecision, ipmQualityErrorBits, ipmQualityRangeExponent]
  exact ⟨by omega, Nat.dvd_mul_right 4 _, by omega, by omega, by omega⟩

/-- Exact fixed-point representation of `cfg.ε` for `concreteCirculationCfgWithLast`. -/
private theorem dry_cfg_eps_eq {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (SparseCore.lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (J : Circulation) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let P := ipmQualityPrecision I.m V k
    let epsExp := k + Num.IPM.alphaExponent I.m V + 10
    (concreteCirculationCfgWithLast W J).ε =
      ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P := by
  intro I V k P epsExp
  have hle : epsExp ≤ P := (dry_ipmQuality_arith I.m V k).2.2.2.1
  dsimp only [concreteCirculationCfgWithLast, concreteCirculationCfgOfDims,
    Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
  have h1024 : (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) := by norm_num
  rw [h1024]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have h2e : (0 : ℝ) < (2 : ℝ) ^ epsExp := by positivity
  have hpow : (2 : ℝ) ^ (P - epsExp) * (2 : ℝ) ^ epsExp = (2 : ℝ) ^ P := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  push_cast
  rw [eq_div_iff h2pos.ne']
  calc (1 / (2 : ℝ) ^ k) * (1 / (2 : ℝ) ^ Num.IPM.alphaExponent I.m V) / (2 : ℝ) ^ 10 *
        (2 : ℝ) ^ P
      = (2 : ℝ) ^ P /
          ((2 : ℝ) ^ k * (2 : ℝ) ^ Num.IPM.alphaExponent I.m V * (2 : ℝ) ^ 10) := by ring
    _ = (2 : ℝ) ^ P / (2 : ℝ) ^ epsExp := by
        dsimp only [epsExp]; rw [pow_add, pow_add]
    _ = (2 : ℝ) ^ (P - epsExp) := by
        rw [div_eq_iff h2e.ne']; exact hpow.symm

/-- The target root edge capacity `initTargetCap cfg G` together with `G.n` fits under
`dryCapLimit dryWitnessUsed J`. -/
theorem dry_initTargetCap_le_capLimit (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e) :
    let G := namedInstance (solverConnectedAugmented J)
    G.n + initTargetCap (concreteCirculationCfgWithLast dryWitnessUsed J) G + 2 ≤
      dryCapLimit dryWitnessUsed J := by
  intro G
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of (le_max_left dryWitnessUsed.M_thresh _)
    (le_max_right dryWitnessUsed.M_thresh _) (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed)
    J hJn hJm hCap
  have hInEq : G.n = (solverConnectedAugmented J).n := by simp [G, namedInstance, MGraph.n]
  have hImPos : 0 < (solverConnectedAugmented J).m :=
    lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  have hImLe : (solverConnectedAugmented J).m ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.M₀ := le_max_left _ _
  have heq := initRootECap_eq_initTargetCap (cfg := concreteCirculationCfgWithLast dryWitnessUsed J) (G := G) rfl hImPos rfl hImLe
  have hle4 := initRootECap_le_four_mul (k := (concreteCirculationCfgWithLast dryWitnessUsed J).P.k) hImLe
  change G.n + initTargetCap (concreteCirculationCfgWithLast dryWitnessUsed J) G + 2 ≤
    12 * (concreteCirculationCfgWithLast dryWitnessUsed J).P.M₀ + 4
  have hN0 : (concreteCirculationCfgWithLast dryWitnessUsed J).N₀ =
      4 * (concreteCirculationCfgWithLast dryWitnessUsed J).P.M₀ := rfl
  change (solverConnectedAugmented J).n ≤
      4 * (concreteCirculationCfgWithLast dryWitnessUsed J).P.M₀ at hIn
  rw [← heq, hN0]
  omega

/-- The caps `(n, m)` of the input graph of the dry run fit under the cap limit. -/
theorem dry_inputCaps_le_capLimit (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e) :
    (namedInstance (solverConnectedAugmented J)).n + (solverConnectedAugmented J).m + 2 ≤
      dryCapLimit dryWitnessUsed J := by
  have h := dry_initTargetCap_le_capLimit J hJn hJm hCap
  have hm : (solverConnectedAugmented J).m ≤
      initTargetCap (concreteCirculationCfgWithLast dryWitnessUsed J) (namedInstance (solverConnectedAugmented J)) := by
    unfold initTargetCap; rw [namedInstance_m]; omega
  omega

/-- Discharges `OrdInitConcreteSpecW` in `dryLinkedProgram` via `initConcreteBody_meets_spec`
when `openInner.toInnerCode` is installed, discharging all 22 concrete code, placement, format,
numeric, graph, and word-size hypotheses automatically and taking only the explicit
bridge hypotheses. -/
theorem dryInitConcrete_meets_spec
    (sc : SparseCoreCode) (openInner : SolverInnerOpen)
    (allocationCoefficient allocationDegree : ℕ)
    (hWordCoeff :
      Classical.choose (concrete_solver_word_bounds_poly dryWitnessUsed) ≤ allocationCoefficient)
    (hSCWordCoeff :
      Classical.choose (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed) ≤
        allocationCoefficient)
    (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    {P_sc : SparseCoreOrdParams} {coreAlloc lastAlloc : ℕ → List ℕ → ℕ}
    {coreInitSpace : ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs (concreteCirculationCfgWithLast dryWitnessUsed J).T)}
    {B_tree : ℤ}
    {paramSpace paramCost lastMult stretchP lastSpace initSpace' initFixed toolMul : ℕ}
    (hlocalCore : Rcore.Local)
    (hThrB : (2 : ℤ) ^ ((ipmQualityMinRatioFormat (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) hw).fmt.precision +
        2 * (ipmQualityMinRatioFormat (solverConnectedAugmented J).m (solverPenalty J.m)
          (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
            (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) hw).rangeExponent + 1) ≤ B_tree)
    (hCapTree : 2 * ((2 * (namedInstance (solverConnectedAugmented J)).n + 1 : ℕ) : ℤ) * B_tree <
      (Num.capacity 4 (ipmQualityMinRatioFormat (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) hw).limbs : ℤ))
    (hParam :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
      let p := dryLinkedProgram dryWitnessUsed sc openInner.toInnerCode
      MeetsContract w p (dryParamSetupProc sc openInner)
        (initParamSetupContract w I.m V F.limbs F.fmt.precision cfg.P.d cfg.P.k
          ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10) cfg.N₀
          (Expander.chosenL (max I.m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2))
          (levelM cfg.TP cfg.P) paramSpace paramCost))
    (hCoreImpl :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let depth := Expander.chosenL (max I.m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2)
      let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
      let p := dryLinkedProgram dryWitnessUsed sc openInner.toInnerCode
      let lay := dryTailLay sc openInner.toInnerCode
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ i < cfg.P.d,
          Rcore.Implements w p lay.scInit lay.scOp
            (sparseCoreOrdMachineContractKFBL F.fmt F.limbs depth cfg.T (chain.G i) cfg.P.k
              (levelM cfg.TP cfg.P i) cfg.N₀ G.n (initTargetCap cfg G) dryCapExp P_sc coreAlloc) ∧
          SparseCoreReadoutFootAt F.fmt F.limbs depth cfg.T (chain.G i) cfg.P.k
            (levelM cfg.TP cfg.P i) cfg.N₀ G.n (initTargetCap cfg G) dryCapExp P_sc coreAlloc Rcore p lay.scOp)
    (hLastImpl :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
      let p := dryLinkedProgram dryWitnessUsed sc openInner.toInnerCode
      let lay := dryTailLay sc openInner.toInnerCode
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ vc ec, vc + ec + 2 ≤ dryCapLimit dryWitnessUsed J →
          (lastLevelRepresentation vc ec 4 F.limbs F.fmt.precision (chain.G cfg.P.d).E).Implements
            w p lay.lastInit lay.lastOp
            (lastLevelRuntimeMachineContract F.fmt F.limbs dryLastTool (chain.G cfg.P.d) vc ec
              lastMult stretchP lastAlloc))
    (hLastSpaceLe : ∀ args, lastAlloc 1 args ≤ lastSpace)
    (hInitSpaceLe :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let depth := Expander.chosenL (max I.m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2)
      ∀ i < cfg.P.d, ∀ g l gr o h,
        coreAlloc 6 [g, l, gr, o, cfg.P.k, levelM cfg.TP cfg.P i, cfg.N₀, F.limbs,
          F.fmt.precision, depth, h] ≤ coreInitSpace i)
    (hCoreLenFits :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        (∀ e ∈ G.E, ∃ q₀ : ℤ, (q₀ : ℝ) / (2 : ℝ) ^ F.fmt.precision = ℓ₀ e) →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ i < cfg.P.d, ∀ e ∈ (chain.G (i + 1)).E,
          ∃ q : ℤ, Num.Fits 4 F.limbs q ∧ (q : ℝ) / (2 : ℝ) ^ F.fmt.precision =
            chain.toTreeChain.chainLen ℓ₀ (i + 1) e)
    (hLastStretchFits :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ e ∈ (chain.G cfg.P.d).E,
          2 * (2 : ℝ) ^ stretchP *
            lastLevelStretchBound (chain.G cfg.P.d) (chain.toTreeChain.chainLen ℓ₀ cfg.P.d) e <
          Num.capacity 4 F.limbs)
    (hSpaceLe :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      initConcreteSpace I.m (namedInstance I).n F.limbs cfg.P.d paramSpace dryCapExp
        (dryCapLimit dryWitnessUsed J) lastSpace
        (LinkCut.PathProg.arenaEnd 0 (namedInstance I).n F.limbs)
        (20 * LinkCut.PathProg.treeLimbs F.limbs + 100)
        coreInitSpace (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀ ≤
      initSpace')
    (hFixedLe :
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      initConcreteFixed I.m (namedInstance I).n F.limbs cfg.P.d paramCost dryCapExp
        (dryCapLimit dryWitnessUsed J) lastMult LinkCut.PathProg.pathC P_sc
        (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀ ≤
      initFixed)
    (hMulLe : max P_sc.mul lastMult ≤ toolMul) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
    let p := dryLinkedProgram dryWitnessUsed sc openInner.toInnerCode
    let lay := dryTailLay sc openInner.toInnerCode
    OrdInitConcreteSpecW w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
      (k + Num.IPM.alphaExponent I.m V + 10) cfg Rcore (namedInstance I) p lay.initConcrete
      B_tree dryCapExp (concreteReadout2LimbMul dryWitnessUsed) (dryCapLimit dryWitnessUsed J)
      P_sc.wordExp initSpace' initFixed toolMul := by
  intro I V k F cfg w p lay
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let cycle := dryCycle threshold A sc openInner.toInnerCode
  let dispatch := mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase) cycle.length
  let forest := dynLctForestBodies 4 (mrdsCycleBase + cycle.length)
  have hfit := ipm_quality_parameter_words_fit I.m V k hw
  have hw14 : 14 ≤ w := hfit.1
  have hArith := dry_ipmQuality_arith I.m V k
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hGV : (namedInstance I).IsValid :=
    namedInstance_valid I (connectedInitialInstance_valid J.toInstance (V : ℤ) J.toInstance_valid)
  have hGE : (namedInstance I).E = Finset.range I.m := rfl
  have hInEq : (namedInstance I).n = I.n := by simp [namedInstance, MGraph.n]
  have hVlt : ∀ v ∈ (namedInstance I).V, v < (namedInstance I).n := fun v hv => by
    rw [hInEq]; exact Finset.mem_range.mp hv
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of (le_max_left dryWitnessUsed.M_thresh _)
    (le_max_right dryWitnessUsed.M_thresh _) (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed)
    J hJn hJm hCap
  have hmG : (namedInstance I).m ≤ cfg.P.M₀ := by rw [namedInstance_m]; exact le_max_left _ _
  have hnG : (namedInstance I).n ≤ cfg.N₀ := by rw [hInEq]; exact hIn
  have hImPos : 0 < I.m := lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  have heCapEq : initRootECap cfg.N₀ cfg.P.k I.m = initTargetCap cfg (namedInstance I) :=
    initRootECap_eq_initTargetCap rfl hImPos rfl (le_max_left _ _)
  have hcap0 : (namedInstance I).n + initRootECap cfg.N₀ cfg.P.k I.m + 2 ≤ dryCapLimit dryWitnessUsed J :=
    heCapEq.symm ▸ dry_initTargetCap_le_capLimit J hJn hJm hCap
  have hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hεPos : 0 < cfg.ε := by
    dsimp only [cfg, concreteCirculationCfgWithLast, concreteCirculationCfgOfDims,
      Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
    positivity
  have hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent := by
    dsimp only [cfg, concreteCirculationCfgWithLast, concreteCirculationCfgOfDims,
      Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
    have hk1 : (1 : ℝ) / 2 ^ k ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    have ha1 : (1 : ℝ) / 2 ^ Num.IPM.alphaExponent I.m V ≤ 1 :=
      div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    have hprod : (1 : ℝ) / 2 ^ k * (1 / 2 ^ Num.IPM.alphaExponent I.m V) ≤ 1 := by
      calc (1 : ℝ) / 2 ^ k * (1 / 2 ^ Num.IPM.alphaExponent I.m V)
          ≤ 1 * 1 := mul_le_mul hk1 ha1 (by positivity) (by norm_num)
        _ = 1 := one_mul 1
    have hE1 : (1 : ℝ) ≤ 2 ^ F.rangeExponent := one_le_pow₀ (by norm_num)
    have hnn : (0 : ℝ) ≤ 1 / 2 ^ k * (1 / 2 ^ Num.IPM.alphaExponent I.m V) := by positivity
    linarith
  obtain ⟨hQuotaBoundW, h4M3W⟩ :=
    Classical.choose_spec (concrete_solver_word_bounds_poly dryWitnessUsed)
      allocationCoefficient allocationDegree hWordCoeff source J hJn hJm hCap hw
  have hNw : cfg.N₀ < 2 ^ w :=
    lt_of_le_of_lt (by change 4 * cfg.P.M₀ ≤ 4 * cfg.P.M₀ + 3; omega) h4M3W
  have hDW : Expander.chosenL (cfg.P.M₀ ^ 2) < 2 ^ w := by
    have hM1 : 1 ≤ cfg.P.M₀ := le_trans (by omega : 1 ≤ 2)
      ((concreteEdgeThresholdWithLast_ge_two dryWitnessUsed).trans (le_max_right _ _))
    exact lt_of_le_of_lt ((chosenL_sq_le_four_mul_add_one hM1).trans
      (by change 4 * cfg.P.M₀ + 1 ≤ 4 * cfg.P.M₀ + 3; omega)) h4M3W
  have hwk : cfg.P.k < 2 ^ w := by
    have hpsi1 : 1 ≤ alg2PsiGameNat ⌈cfg.Ψ⌉₊ cfg.P.M₀ := by unfold alg2PsiGameNat; omega
    have h1 : cfg.P.k ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k := by
      unfold shiftQuotaBase; exact Nat.le_mul_of_pos_left _ (by omega)
    have h2 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ≤
        shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_self_pow (by omega) _
    have h3 : shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) ≤
        (2 * (namedInstance I).m + 2) * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact lt_of_le_of_lt ((h1.trans h2).trans h3) hQuotaBoundW
  have hB14 : 2 ^ 14 * ipmQualityParameterBound I.m V k < 2 ^ w := by
    have hsz : ipmQualityParameterBound I.m V k < 2 ^ (ipmQualityParameterBound I.m V k).size :=
      Nat.lt_size_self _
    calc 2 ^ 14 * ipmQualityParameterBound I.m V k
        < 2 ^ 14 * 2 ^ (ipmQualityParameterBound I.m V k).size :=
          Nat.mul_lt_mul_of_pos_left hsz (by decide)
      _ = 2 ^ (14 + (ipmQualityParameterBound I.m V k).size) := (pow_add 2 _ _).symm
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
  have hsearchW : 20 * (4 * F.limbs + 8) + 100 < 2 ^ w := by
    have hLle : F.limbs ≤ ipmQualityParameterBound I.m V k := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityParameterBound]; omega
    have hB1 : 1 ≤ ipmQualityParameterBound I.m V k := by unfold ipmQualityParameterBound; omega
    exact lt_of_le_of_lt (by omega : 20 * (4 * F.limbs + 8) + 100 ≤ 2 ^ 14 * ipmQualityParameterBound I.m V k) hB14
  have hVW : V < 2 ^ w := hfit.2.2.2.2.2.2.2
  have hPW : F.fmt.precision < 2 ^ w := hfit.2.2.1
  have hImGeJm : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCap).1
  have hInLe : I.n ≤ 2 * I.m + 2 := by
    change J.n + 1 ≤ 2 * I.m + 2; omega
  have h2n1Le : 2 * (namedInstance I).n + 1 ≤ 4 * I.m + 5 := by rw [hInEq]; omega
  have hvw : 2 * (namedInstance I).n + 1 < 2 ^ w := by
    have hMle : I.m ≤ ipmQualityParameterBound I.m V k := by unfold ipmQualityParameterBound; omega
    have hB1 : 1 ≤ ipmQualityParameterBound I.m V k := by unfold ipmQualityParameterBound; omega
    exact lt_of_le_of_lt (by omega : 2 * (namedInstance I).n + 1 ≤ 2 ^ 14 * ipmQualityParameterBound I.m V k) hB14
  have hwidthN : Nat.log 2 (2 * (namedInstance I).n + 1) ≤ 4 * F.limbs := by
    have hlog1 : Nat.log 2 (2 * (namedInstance I).n + 1) ≤ (4 * I.m + 5).size := by
      calc Nat.log 2 (2 * (namedInstance I).n + 1)
          ≤ Nat.log 2 (4 * I.m + 5) := Nat.log_mono_right h2n1Le
        _ ≤ (4 * I.m + 5).size :=
            le_of_lt (Nat.log_lt_of_lt_pow (by omega) (Nat.lt_size_self _))
    have hsz : (4 * I.m + 5).size ≤ I.m.size + 4 := by
      rw [Nat.size_le]
      have h1 : I.m < 2 ^ I.m.size := Nat.lt_size_self I.m
      have h2 : 1 ≤ 2 ^ I.m.size := Nat.one_le_pow _ _ (by decide)
      rw [pow_add]; omega
    have hmsz : I.m.size ≤ F.rangeExponent + 8 := by
      have h1 : I.m.size ≤ (I.m.size + V.size) ^ 2 :=
        le_trans (Nat.le_add_right _ _) (Nat.le_self_pow (by decide : 2 ≠ 0) _)
      have h2 := slackRangeExponent_le_qualitySlackExponent I.m V k
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityRangeExponent]
      unfold slackRangeExponent at h2
      omega
    have h4L : F.rangeExponent + 12 ≤ 4 * F.limbs := by
      dsimp only [F, ipmQualityMinRatioFormat, ipmQualityLimbs, ipmQualityPrecision]
      omega
    omega
  have hMw : ∀ i < cfg.P.d, levelM cfg.TP cfg.P i < 2 ^ w := by
    intro i hi
    have hL := (concrete_sparseCoreCapHyp_uniform dryWitnessUsed J hJn hJm hCap i hi.le 0 0 (by omega)).2
    have h1 := Classical.choose_spec (concrete_sparseCoreWordBound_uniform_lt_two_pow_wordSize dryWitnessUsed)
      allocationCoefficient allocationDegree hSCWordCoeff source J hJn hJm hCap hw
      1 (by decide) i _ hL
    have hpos : 1 ≤ F.limbs + 1 := Nat.succ_pos _
    have hle : levelM cfg.TP cfg.P i ≤ (levelM cfg.TP cfg.P i + cfg.N₀ + 2) ^ 1 * (F.limbs + 1) := by
      rw [pow_one]
      exact le_trans (by omega) (Nat.le_mul_of_pos_right _ hpos)
    exact lt_of_le_of_lt hle h1
  -- Extract all concrete procedure placements and helper contracts from `dryLinkedProgram`
  have hOps := solverOpsProcs_initHelpers hw14 (solverOps_hasAt threshold A dispatch sc openInner.toInnerCode forest)
  have hInnerAll := dryInner_hasAt threshold A dispatch sc openInner.toInnerCode forest
  have hInitBlock : p.HasAt lay.innerBase
      (dryInitConcreteProcs (solverTailInnerEnv mrdsCycleBase lastGuest ⌈max 1 lastCanonConst⌉₊
          lastWordConst sc solverTailBase)
        (dryParamSetupProc sc openInner)) :=
    Num.hasAt_append_left hInnerAll
  have hLocal := dryInitConcreteProcs_hasAt (w := w) hInitBlock
  have hLastReadout : p.procs[lay.lastOp 0]? = some LastLevelProgram.readoutBody :=
    packedLastLevelBodies_readout_at
      (solverCycle_lastLevel_hasAt threshold A dispatch lastGuest ⌈max 1 lastCanonConst⌉₊
        lastWordConst sc openInner.toInnerCode forest)
  have hEq : ToolInitOrdEqOnE cfg.T :=
    sparseCoreBundleRestartToolMachWith_initOrdEqOnE _ _ _ _ _ _
  have hLastEq : LastLevelBuildEqOnE cfg.L :=
    fixedPointLastLevelTool_buildEqOnE _ _
  have hCoreSpec := initConcreteBody_meets_spec
    (w := w) (L := F.limbs) (P := F.fmt.precision) (E := F.rangeExponent) (m := I.m) (V := V)
    (psi := ⌈cfg.Ψ⌉₊) (k := k) (epsExp := k + Num.IPM.alphaExponent I.m V + 10)
    (capExp := dryCapExp) (limbMul := concreteReadout2LimbMul dryWitnessUsed)
    (capLimit := dryCapLimit dryWitnessUsed J) (initConcreteProc := lay.initConcrete)
    (graphPack := lay.innerBase + 17 + dgIdxInitFromLists) (paramSetup := dryParamSetupProc sc openInner)
    (sortedEnds := lay.innerBase + 1) (coreInit := lay.scInit) (coreLenProc := lay.innerBase + 2)
    (edgeProc := lay.innerBase + 3) (signExt := mrdsCycleBase + 17) (mul := mrdsCycleBase + 11)
    (intDiv := mrdsCycleBase + 22) (lastInit := lay.lastInit) (treeBase := mrdsCycleBase + 81)
    (bind := lay.innerBase + 4) (shift := mrdsCycleBase + 20) (divide := mrdsCycleBase + 16)
    (negate := mrdsCycleBase + 4) (copy := mrdsCycleBase)
    (lastMult := lastMult) (stretchP := stretchP) (lastSpace := lastSpace)
    (paramSpace := paramSpace) (paramCost := paramCost)
    (fmt := F.fmt) (cfg := cfg) (P_sc := P_sc) (coreAlloc := coreAlloc) (lastAlloc := lastAlloc)
    (coreInitSpace := coreInitSpace) (Rcore := Rcore) (opCore := lay.scOp) (opLast := lay.lastOp)
    (G := namedInstance I) (p := p) (B_tree := B_tree)
    (by simpa only [lay, dryTailLay, solverTailLayout, solverTailInnerEnv, SolverInnerOpen.toInnerCode, Nat.add_zero] using hLocal.1)
    rfl rfl hArith.1 hEq hLastEq hlocalCore hVcfg hGV hGE hVlt hmG hnG hcap0 hEΨ
    (dry_cfg_eps_eq dryWitnessUsed J) hεPos hεLe hThrB hCapTree
    cfg.P.hd hw14 hwk h4M3W hVW hPW hDW hsearchW hArith.2.1 hArith.2.2.1 hArith.2.2.2.1 hArith.2.2.2.2
    hvw hwidthN hMw
    (hLocal.2.2.2.2.2 _ _ _ _ _) hParam hLocal.2.1 hLocal.2.2.1 hLocal.2.2.2.1
    hOps.2.2.2.2.1 hOps.2.2.1 hOps.2.2.2.2.2.2.1 hOps.2.2.2.2.2.1 hOps.2.2.2.1 hOps.2.1 hOps.1
    hLocal.2.2.2.2.1 hOps.2.2.2.2.2.2.2
    (fun ℓ₀ g₀ hL i hi => by rw [heCapEq]; exact hCoreImpl ℓ₀ g₀ hL i hi) hLastImpl hLastReadout hLastSpaceLe hInitSpaceLe hCoreLenFits hLastStretchFits
  exact ordInitConcreteSpecW_mono hCoreSpec hSpaceLe hFixedLe hMulLe

end MinCostFlow.Final.DryRun

end
