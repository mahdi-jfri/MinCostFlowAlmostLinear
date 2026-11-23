module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunFactsKFBL
import WordRAM.Tactic

/-!
# Where the levels lie after the exit of Branch B (`WireChainCoreBranchBLevelLocKFBL`)

The suffix of Branch B writes only the root directory, the edge accounts (tags `9`, …, `16`
except `12`) and the tree. So a word keeps its value across the suffix when it lies in one of
three zones: below `uIntBuf` with a tag of at least `17`, in `[uIntBuf, heap)`, or in the heap
`[sE.regs 4, sX.regs 4)` of the exit (`BranchBSufZoneKFBL`, `suffix_keep_zone`).

`BranchBExitLevelLocKFBL` says that the new last level, the level graphs and the length blocks
after the exit lie in these zones. With it, the fields `lastRep`, `graphs` and `lens` of
`BranchBSufOutKFBL` follow from the exit facts (`own_levels`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The zones the suffix of Branch B keeps: below `uIntBuf` with a tag of at least `17`, in
`[uIntBuf, selBase)`, or in `[lo, hi)`. -/
@[expose] def BranchBSufZoneKFBL (tag : ℕ → ℕ) (uIntBuf selBase lo hi a : ℕ) : Prop :=
  (a < uIntBuf ∧ 17 ≤ tag a) ∨ (uIntBuf ≤ a ∧ a < selBase) ∨ (lo ≤ a ∧ a < hi)

/-- The words of the new last level, the level graphs and the length blocks after the exit of
Branch B lie in the zones the suffix keeps. -/
structure BranchBExitLevelLocKFBL {L P vCap eCap : ℕ} {cfg : Alg2Config} (tag : ℕ → ℕ)
    (uIntBuf : ℕ) (A : BranchBAddrs) (vcL ecL : ℕ) (X : ChainState cfg.T cfg.P) (sE out : State)
    (termTokN : ℕ) : Prop where
  last : ∀ a, (LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P (X.G cfg.P.d).E).foot
      (out.mem (A.handleBase + cfg.P.d)) termTokN a →
    BranchBSufZoneKFBL tag uIntBuf A.selBase (sE.regs 4) (out.regs 4) a
  graph : ∀ j < cfg.P.d, ∀ a, out.mem (A.levelMeta + cfg.P.d + j) ≤ a →
    a < out.mem (A.levelMeta + cfg.P.d + j) + dynGraphSize vCap eCap →
    BranchBSufZoneKFBL tag uIntBuf A.selBase (sE.regs 4) (out.regs 4) a
  len : ∀ j < cfg.P.d, ∀ e ∈ (X.G j).E, ∀ i < L,
    BranchBSufZoneKFBL tag uIntBuf A.selBase (sE.regs 4) (out.regs 4)
      (out.mem (A.levelMeta + j) + e * L + i)

namespace BranchBRunKFBL

variable {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
      collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {stepCap : ℕ → ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}

variable (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)

/-- A word in a zone of `BranchBSufZoneKFBL` keeps its value across the suffix of Branch B. -/
theorem suffix_keep_zone {a : ℕ}
    (ha : BranchBSufZoneKFBL tok.tag uIntBuf heap (H.sE.regs 4) (H.sX.regs 4) a) :
    H.out.mem a = H.sX.mem a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
  obtain ⟨hOwn, hT1, _⟩ := hTags
  obtain ⟨hU, hh0, hS1h, hFl, hX⟩ := heap_order H
  obtain ⟨_, _, _, _, _, _, _, _, _, hTreeFoot, _⟩ := H.pre
  obtain ⟨_, _, _, _, _, _, _, _, _, hFr, _⟩ := H.suf
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact suffix_keep_low H h1 (by omega) (by omega)
  · exact suffix_keep_mid H h1 (by omega)
  · refine hFr a h2 (fun he => by
        have := H.start.footLt _ (Or.inl (hOwn _ (by rw [hT1 11 (by omega)]; decide))); omega)
      (fun h => absurd h (by omega)) (fun _ hf => ?_)
    rcases hTreeFoot a hf with h | h
    · have := H.start.footLt a (Or.inr (Or.inl h)); omega
    · omega

/-- The meta words of the levels keep their values across the suffix of Branch B: they lie below
`uIntBuf` with the tag `22 + d`. -/
theorem suffix_keep_meta {j : ℕ} (hj : j < 2 * cfg.P.d) :
    H.out.mem (solverLevelMetaAddr tok.table cfg.P.d + j) =
      H.sX.mem (solverLevelMetaAddr tok.table cfg.P.d + j) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
  obtain ⟨hOwn, _⟩ := hTags
  obtain ⟨_, _, _, _, hMT, _⟩ := H.start.meta0
  have ht := hMT j hj
  have hlt := H.start.footLt _ (Or.inl (hOwn _ (by rw [ht]; omega)))
  exact suffix_keep_low H hlt (by rw [ht]; omega) (by rw [ht]; omega)

/-- The fields `lastRep`, `graphs` and `lens` of `BranchBSufOutKFBL` at the end of a run of
Branch B, from the exit facts and the places of the levels after the exit. -/
theorem own_levels
    (hLoc : BranchBExitLevelLocKFBL (L := L) (P := P) (vCap := vCap) (eCap := eCap) tok.tag
      uIntBuf H.A H.vcL H.ecL H.X H.sE H.sX H.termTokN) :
    (LastLevelProgram.lastLevelRepresentation H.vcL H.ecL 4 L P
        ((alg2PreResetState cfg model U
          (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
          (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.G
          cfg.P.d).E).rep
      (H.out.mem (tok.handle + 18 + cfg.P.d))
      ((alg2PreResetState cfg model U
          (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
          (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.lastK,
        (alg2PreResetState cfg model U
          (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
          (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.lastLSFs)
      H.termTokN H.out.mem ∧
    (∀ j < cfg.P.d,
      DynGraphAt H.out.mem (H.out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j))
        vCap eCap
        ((alg2PreResetState cfg model U
          (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
          (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.G j)) ∧
    (∀ j < cfg.P.d,
      EdgeValuesAt H.out.mem (H.out.mem (solverLevelMetaAddr tok.table cfg.P.d + j)) 4 L P
        ((alg2PreResetState cfg model U
          (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
          (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.G j).E
        ((alg2PreResetState cfg model U
          (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
          (updateOverlay model.extG.E U (readVector mem0 l 4 L P m)
            model.extℓ)).chain.toTreeChain.chainLen
          (alg2PreResetState cfg model U
            (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
            (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.ℓ j)) := by
  have hX : H.X = (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
    rw [H.modelEq, H.gVec_eq, H.lVec_eq]
  have hHB : H.A.handleBase = tok.handle + 18 := by rw [H.A_eq]; rfl
  have hLM : H.A.levelMeta = solverLevelMetaAddr tok.table cfg.P.d := by rw [H.A_eq]; rfl
  have hSB : H.A.selBase = heap := by rw [H.A_eq]; rfl
  have hZ {a : ℕ} (ha : BranchBSufZoneKFBL tok.tag uIntBuf H.A.selBase (H.sE.regs 4)
      (H.sX.regs 4) a) : H.out.mem a = H.sX.mem a := by
    rw [hSB] at ha
    exact suffix_keep_zone H ha
  rw [← hX]
  refine ⟨?_, fun j hj => ?_, fun j hj => ?_⟩
  · have hK : H.out.mem (tok.handle + 18 + cfg.P.d) = H.sX.mem (tok.handle + 18 + cfg.P.d) :=
      suffix_keep_handle H le_rfl
    have hR := H.exitOut.lastRep
    have hF := hLoc.last
    rw [hHB] at hR hF
    rw [hK]
    exact (LastLevelProgram.lastLevelRepresentation_local _ _ _ _ _ _ _ _ _ _ _
      (fun a ha => (hZ (hF a ha)).symm)).1 hR
  · have hK : H.out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) =
        H.sX.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) := by
      rw [Nat.add_assoc]; exact suffix_keep_meta H (by omega)
    have hG := H.exitOut.graphs j hj
    have hF := hLoc.graph j hj
    rw [hLM] at hG hF
    rw [hK]
    exact hG.of_agree fun a h1 h2 => hZ (hF a h1 h2)
  · have hK : H.out.mem (solverLevelMetaAddr tok.table cfg.P.d + j) =
        H.sX.mem (solverLevelMetaAddr tok.table cfg.P.d + j) := suffix_keep_meta H (by omega)
    have hV := H.exitOut.lens j hj
    have hF := hLoc.len j hj
    rw [hLM] at hV hF
    rw [hK]
    exact hV.congr fun e he i hi => hZ (hF e he i hi)

end BranchBRunKFBL

end MinCostFlow.MinRatio
