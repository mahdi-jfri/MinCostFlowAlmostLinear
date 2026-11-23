module

public import MinCostFlow.MinRatio.WireChainCoreBranchARunKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchATokHypKFBL
import WordRAM.Tactic

/-!
# All of Branch A: the program facts and the statement (`WireChainCoreBranchAEnvKFBL`)

Branch A of the chain core rebuilds every level. Its statement `wireBranchAKFBL` runs, in
order, Steps 0–2 (`wireBranchASteps0To2StmtKFBL`), Step 3 (`wireBranchAStep3StmtKFBL`),
Step 4 (`wireBranchASuffixStmtKFBL`) and Step 5 (`wireBranchASync2AndReadyStmt`). Each part has
its own run lemma. The run of the whole branch is in `WireChainCoreBranchAAllKFBL.lean`.

This file holds what that run needs besides the run lemmas of the parts:
* `BranchAEnvKFBL`: the facts on the program and on the fixed sizes, which do not depend on the
  model. With it, the run lemma of the whole branch takes only the facts of the model and of the
  memory.
* `updateLoopModelInv_rebuild_zero`: when level `0` is rebuilt, the loop invariant of the model
  gives the rebuild invariant that Step 4 needs.
* `branchA_frame0_tag`, `branchA_frame0_root`: the words of the solver header that Steps 0–4 do
  not write keep their old values. The tree sync of Step 5 needs them.
* `treeEditNamedSlots_empty_noEdge`: a tree with no named edges has no edge slots.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- Branch A of the chain core: Steps 0–2, Step 3, Step 4 and Step 5, in this order. -/
@[expose] def wireBranchAKFBL (packEditsProc readTree cutTree linkTree bind canonCopy isNeg
    refreshAccountsProc dgApply updateLen0Proc readLSF renameProc compactProc sortedEndsProc
    initCore readGraph coreLenProc readOrd lastInit rebuildOffReadyProc : ℕ) : Stmt :=
  wireBranchASteps0To2StmtKFBL packEditsProc readTree cutTree linkTree bind canonCopy isNeg
    refreshAccountsProc dgApply updateLen0Proc readLSF ;;
  wireBranchAStep3StmtKFBL renameProc compactProc sortedEndsProc ;;
  wireBranchASuffixStmtKFBL initCore readGraph readLSF coreLenProc readOrd lastInit ;;
  wireBranchASync2AndReadyStmt packEditsProc readTree cutTree linkTree bind canonCopy isNeg
    rebuildOffReadyProc

theorem wireBranchAKFBL_noRand (packEditsProc readTree cutTree linkTree bind canonCopy isNeg
    refreshAccountsProc dgApply updateLen0Proc readLSF renameProc compactProc sortedEndsProc
    initCore readGraph coreLenProc readOrd lastInit rebuildOffReadyProc : ℕ) :
    (wireBranchAKFBL packEditsProc readTree cutTree linkTree bind canonCopy isNeg
      refreshAccountsProc dgApply updateLen0Proc readLSF renameProc compactProc sortedEndsProc
      initCore readGraph coreLenProc readOrd lastInit rebuildOffReadyProc).NoRand := by
  simp only [wireBranchAKFBL, Stmt.NoRand]
  exact ⟨wireBranchASteps0To2StmtKFBL_noRand _ _ _ _ _ _ _ _ _ _ _,
    wireBranchAStep3StmtKFBL_noRand _ _ _, wireBranchASuffixStmtKFBL_noRand _ _ _ _ _ _,
    wireBranchASync2AndReadyStmt_noRand _ _ _ _ _ _ _ _⟩

/-- The facts on the program and on the fixed sizes that Branch A uses. None of them depends on
the model: the procedures of the program, the contracts that its helper procedures meet, the
budget forms `UpdateCoreOpsHypKFBL`, and the bounds on the fixed sizes. The procedures of the
path tree and of the level cores are the entries `opTree j` and `opCore j`. -/
structure BranchAEnvKFBL (w L P m capExp capLimit fcap lastMul intCapMax forestEdgeCap drainUnit
    edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
    refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply updateLen0Proc
    initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc signExt mul
    intDiv lastInit rebuildOffReadyProc : ℕ) (coreSpace coreFixed : ℕ → ℕ) (toolMul : ℕ)
    (fmt : Num.Format w) (cfg : Alg2Config) (G : MGraph) (Psc : SparseCoreOrdParams)
    (levelSpace : ℕ → ℕ) (levelCost : ChainState cfg.T cfg.P → ℕ → ℕ)
    (updStepSpace : ℕ → ℕ → ℕ) (lastSpace termUpdSpace : ℕ)
    (allocation lastAlloc : ℕ → List ℕ → ℕ) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (p : Program) (opTree opCore opLast : ℕ → ℕ) (stepCap : ℕ → ℕ → ℕ) : Prop where
  coreLocal : Rcore.Local
  four : fmt.limbBits = 4
  prec : fmt.precision = P
  width : P ≤ 4 * L
  lPos : 0 < L
  eCapPos : 0 < eCap
  lW : L < 2 ^ w
  pW : P < 2 ^ w
  depthW : Expander.chosenL (cfg.P.M₀ ^ 2) < 2 ^ w
  dW : cfg.P.d < 2 ^ w
  kPos : 0 < cfg.P.k
  kW : cfg.P.k < 2 ^ w
  nW : cfg.N₀ < 2 ^ w
  w18 : 18 < 2 ^ w
  capLim : vCap + eCap + 2 ≤ capLimit
  initOrdEq : ToolInitOrdEqOnE cfg.T
  wordExpEq : Psc.wordExp = wordExp
  packP : p.procs[packEditsProc]? = some wireSuffixPackEditsBody
  refAccP : p.procs[refreshAccountsProc]? =
    some (wireRefreshAccountsBody shift negate refreshOneProc)
  refOneP : p.procs[refreshOneProc]? =
    some (wireRefreshOneAccountBody divide add sub negate copy isNeg)
  updLen0P : p.procs[updateLen0Proc]? = some (wireUpdateLen0FromBatchBody copy)
  treeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
    (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L))
  bindC : MeetsContract w p bind (pathSlotBindContract w)
  canonC : ∀ v, MeetsContract w p canonCopy (wireCanonCopyContract w v)
  isNegC : MeetsContract w p isNeg (Num.isNegativeContract w 4)
  shiftC : MeetsContract w p shift (Num.shiftLeftContract w 4)
  divC : MeetsContract w p divide (Num.fixedDivideContract w 4)
  addC : MeetsContract w p add (Num.addContract w 4)
  subC : MeetsContract w p sub (Num.subtractContract w 4)
  negC : MeetsContract w p negate (Num.negateContract w 4)
  copyC : MeetsContract w p copy (copyWordsContract w)
  dgApplyC : ∀ (G' : MGraph) (U : List Update) (bW : ℕ),
    MeetsContract w p dgApply (dgApplyBatchContract w vCap eCap G' G' U bW)
  coreImpl : UpdateCoreCoreKFBL fmt L m vCap eCap capExp cfg Psc allocation Rcore p initCore opCore
  renP : p.procs[renameProc]? = some level0RenameBody
  compP : p.procs[compactProc]? = some (wireCompactLevel0Body copy dgInit)
  sortP : p.procs[sortedEndsProc]? = some buildSortedEndsBody
  dgInitC : ∀ (G' : MGraph) vL eTriples,
    MeetsContract w p dgInit (dgInitFromListsContract w vCap eCap G' vL eTriples)
  coreLenP : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc)
  edgeP : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy)
  signC : MeetsContract w p signExt (Num.signExtendContract w 4)
  mulC : MeetsContract w p mul (Num.multiplyContract w 4)
  intDivC : MeetsContract w p intDiv (Num.integerDivideContract w 4)
  lastImpl : ∀ H : MGraph,
    H.m ≤ m → H.m ≤ levelM cfg.TP cfg.P cfg.P.d → H.n ≤ H.m + 1 →
    (∀ u ∈ H.V, ∀ v ∈ H.V, H.Connected u v) →
    (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision H.E).Implements
      w p lastInit opLast
      (lastLevelRuntimeMachineContract fmt L cfg.L H vCap eCap lastMul stretchPrec lastAlloc)
  ops : UpdateCoreOpsHypKFBL (w := w) (L := L) (P := P) (m := m) (capExp := capExp)
    (capLimit := capLimit) (fcap := fcap) (lastMul := lastMul) (intCapMax := intCapMax)
    (forestEdgeCap := forestEdgeCap) (drainUnit := drainUnit) (edMul := edMul)
    (mThresh := mThresh) (coreSpace := coreSpace) (coreFixed := coreFixed) (toolMul := toolMul)
    (fmt := fmt) (cfg := cfg) (G := G) (Psc := Psc) (allocation := allocation)
    (lastAlloc := lastAlloc) levelSpace levelCost updStepSpace lastSpace termUpdSpace stepCap
  rebuildP : p.procs[rebuildOffReadyProc]? = some (wireRebuildOffReadyBody isNeg)

/-- When the rebuild test fires at level `0`, the loop invariant of the model gives the rebuild
invariant at level `0`, on the compact graph and the compact length and gradient vectors. -/
theorem updateLoopModelInv_rebuild_zero {w L P wordExp stretchPrec : ℕ} {cfg : Alg2Config}
    {vcOf ecOf : ℕ → ℕ} {origLen : ℕ → ℕ → ℝ} {ℓ' g' : ℕ → ℝ} {st : ChainState cfg.T cfg.P}
    {curG : MGraph} {curU : List Update} {curEnc : ℕ} {oldOrd : ℕ → List End}
    (hd : 0 < cfg.P.d)
    (h : UpdateLoopModelInv w L P wordExp stretchPrec vcOf ecOf origLen ℓ' g' cfg.P.d 0 st curG
      curU curEnc oldOrd)
    (hOver : intRebuildThreshold cfg.P st.N₀ 0 < st.updCount 0 + curU.length) :
    UpdateRebuildModelInv w L P wordExp stretchPrec st 0 curG.compact
      (fun j => ℓ' (compactUnrank curG.E j)) (fun j => g' (compactUnrank curG.E j)) curEnc := by
  obtain ⟨d', hd'⟩ : ∃ d', cfg.P.d = d' + 1 := ⟨cfg.P.d - 1, by omega⟩
  rw [hd'] at h
  unfold UpdateLoopModelInv at h
  obtain ⟨_, _, _, _, _, h⟩ := h
  rw [ite_eq_left hOver] at h
  exact h.1

/-- A path tree whose named edges form the empty set has no edge slots. -/
theorem treeEditNamedSlots_empty_noEdge {s : PathTreeState} {trees : List AuxTree} {G : MGraph}
    {slot name : ℕ → ℕ} (h : TreeEditNamedSlots s trees { G with E := ∅ } slot name) :
    ∀ sl ∈ trees.flatMap AuxTree.toList, ¬ isEdgeSlot s.n sl :=
  fun sl hsl hEdge => by simpa using (h.inverse sl hsl hEdge).1

section Frame

variable {L P m V psi k epsExp drainUnit root uIntBuf : ℕ} {cfg : Alg2Config}
  {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 M : ℕ → ℕ} {model : Alg2State cfg}
  {tok : SolverToken cfg L Rcore}

/-- The frame that Step 4 of Branch A gives below `uIntBuf`: it changes only the words with the
listed old tags, the two root words `root + 11`, `root + 14`, the level handles and branches,
the rebuild counter of level `0` and the update counters. -/
@[expose] def BranchAFrame0 (root uIntBuf : ℕ) (cfg : Alg2Config) {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (tok : SolverToken cfg L Rcore)
    (mem0 M : ℕ → ℕ) : Prop :=
  let d := cfg.P.d
  let handleBase := tok.handle + 18
  let branchBase := handleBase + (d + 1)
  let rebuildCountBase := tok.levelsEnd + 2 * (d + 1)
  let updCountBase := tok.levelsEnd + 3 * (d + 1)
  ∀ a < uIntBuf, a ≠ root + 11 → a ≠ root + 14 → a ≠ rebuildCountBase →
    (a < handleBase ∨ handleBase + d < a) →
    (a < branchBase ∨ branchBase + d < a) →
    (a < updCountBase ∨ updCountBase + d ≤ a) →
    tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 →
    tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 →
    tok.tag a ≠ 12 → tok.tag a ≠ 13 → tok.tag a ≠ 14 → tok.tag a ≠ 15 →
    tok.tag a ≠ 16 → tok.tag a ≠ 20 →
    tok.tag a ≠ 22 + d → tok.tag a ≠ 23 + d →
    (∀ j < d, tok.tag a ≠ 21 + j) → M a = mem0 a

/-- Under the frame of Step 4, a word whose old tag Steps 0–4 do not write keeps its value. -/
theorem branchA_frame0_tag
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hFr : BranchAFrame0 root uIntBuf cfg tok mem0 M) {a v : ℕ} (ht : tok.tag a = v)
    (hv : v ∉ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20])
    (h22 : v ≠ 22 + cfg.P.d) (h23 : v ≠ 23 + cfg.P.d) (hc : ∀ j < cfg.P.d, v ≠ 21 + j) :
    M a = mem0 a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwn, hT1, _, _, hT4, hT5, _⟩ := hTags0
  have hv' : ∀ c ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20], v ≠ c :=
    fun c hc' h => hv (h ▸ hc')
  have hlt : a < uIntBuf := hFootLt a (Or.inl (hOwn a (ht ▸ hv' 0 (by simp))))
  have hT4' := WireBranchATokHypKFBL.tag_of_block tok.tag hT4
  have hT5' := WireBranchATokHypKFBL.tag_of_block tok.tag hT5
  have hSep := WireBranchATokHypKFBL.tagSep tok.tag
  exact hFr a hlt
    (hSep _ _ _ _ ht (hT1 11 (by omega)) (hv' 1 (by simp)))
    (hSep _ _ _ _ ht (hT1 14 (by omega)) (hv' 1 (by simp)))
    (hSep _ _ _ _ ht (hT5 (2 * (cfg.P.d + 1)) (by omega)) (hv' 5 (by simp)))
    (by by_contra h; push Not at h; exact hv' 4 (by simp) (ht.symm.trans (hT4' _ h.1 (by omega))))
    (by by_contra h; push Not at h; exact hv' 4 (by simp) (ht.symm.trans (hT4' _ (by omega)
      (by omega))))
    (by by_contra h; push Not at h; exact hv' 5 (by simp) (ht.symm.trans (hT5' _ (by omega)
      (by omega))))
    (ht ▸ hv' 6 (by simp)) (ht ▸ hv' 7 (by simp)) (ht ▸ hv' 8 (by simp))
    (ht ▸ hv' 9 (by simp)) (ht ▸ hv' 10 (by simp)) (ht ▸ hv' 11 (by simp))
    (ht ▸ hv' 12 (by simp)) (ht ▸ hv' 13 (by simp)) (ht ▸ hv' 14 (by simp))
    (ht ▸ hv' 15 (by simp)) (ht ▸ hv' 16 (by simp)) (ht ▸ hv' 20 (by simp))
    (ht ▸ h22) (ht ▸ h23) (fun j hj => ht ▸ hc j hj)

/-- Under the frame of Step 4, the root words other than `root + 11` and `root + 14` keep their
values. -/
theorem branchA_frame0_root
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hFr : BranchAFrame0 root uIntBuf cfg tok mem0 M) (j : ℕ) (hj : j < 16) (hne11 : j ≠ 11)
    (hne14 : j ≠ 14) : M (root + j) = mem0 (root + j) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwn, hT1, _, _, hT4, hT5, _⟩ := hTags0
  have h1 := hT1 j hj
  have hT4' := WireBranchATokHypKFBL.tag_of_block tok.tag hT4
  have hT5' := WireBranchATokHypKFBL.tag_of_block tok.tag hT5
  exact hFr (root + j) (hFootLt _ (Or.inl (hOwn _ (by rw [h1]; decide)))) (by omega) (by omega)
    (WireBranchATokHypKFBL.tagSep _ _ _ _ _ h1 (hT5 (2 * (cfg.P.d + 1)) (by omega)) (by decide))
    (by by_contra h; push Not at h; have := hT4' _ h.1 (by omega); omega)
    (by by_contra h; push Not at h; have := hT4' (root + j) (by omega) (by omega); omega)
    (by by_contra h; push Not at h; have := hT5' (root + j) (by omega) (by omega); omega)
    (by rw [h1]; decide) (by rw [h1]; decide) (by rw [h1]; decide)
    (by rw [h1]; decide) (by rw [h1]; decide) (by rw [h1]; decide)
    (by rw [h1]; decide) (by rw [h1]; decide) (by rw [h1]; decide)
    (by rw [h1]; decide) (by rw [h1]; decide) (by rw [h1]; decide)
    (by rw [h1]; omega) (by rw [h1]; omega) (fun _ _ => by rw [h1]; omega)

end Frame

end MinCostFlow.MinRatio
