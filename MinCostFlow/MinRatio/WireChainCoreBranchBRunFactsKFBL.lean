module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunKFBL
import WordRAM.Tactic

/-!
# Facts on a run of Branch B (`WireChainCoreBranchBRunFactsKFBL`)

Short facts on a run `H : BranchBRunKFBL …` that the fields of `BranchBSufOutKFBL` use: the order
of the heap pointers of the parts, the tags of the solver words below `uIntBuf`, and the suffix
frame on the solver words.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

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

/-- The heap pointers of the parts of a run of Branch B are in order: the start `heap`, the heap
floor `heap2` after the prefix, the pointer `sE.regs 4` at the top of the last pass of the loop,
and the pointer `sX.regs 4` after the exit. -/
theorem heap_order :
    uIntBuf ≤ heap ∧ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ H.hS1 ∧
    H.hS1 + 3 * L ≤ H.heap2 ∧ H.heap2 ≤ H.sE.regs 4 ∧ H.sE.regs 4 ≤ H.sX.regs 4 := by
  have h1 := H.start.uLe
  have h2 := H.start.edHeap
  obtain ⟨_, _, _, hh0, _, hS1h, _⟩ := H.pre
  obtain ⟨_, _, hF4, _⟩ := H.front
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hL4, _⟩ := H.loop
  have hX := H.exitOut.heapLo
  refine ⟨by omega, hh0, hS1h, ?_, hX⟩
  rw [hF4] at hL4
  omega


/-- A solver word below `uIntBuf` with a tag outside `1` and `9`, …, `16` keeps its value across
the suffix of Branch B. -/
theorem suffix_keep_low {a : ℕ} (ha : a < uIntBuf) (h1 : tok.tag a ≠ 1)
    (ht : tok.tag a ≠ 9 ∧ tok.tag a ≠ 10 ∧ tok.tag a ≠ 11 ∧ tok.tag a ≠ 13 ∧ tok.tag a ≠ 14 ∧
      tok.tag a ≠ 15 ∧ tok.tag a ≠ 16) :
    H.out.mem a = H.sX.mem a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
  obtain ⟨_, hT1, _⟩ := hTags
  obtain ⟨hU, _, _, _, _⟩ := heap_order H
  have hHeapX := H.exitOut.heapLo
  obtain ⟨_, _, _, _, _, _, _, _, _, hFr, _⟩ := H.suf
  refine hFr a ?_ (fun he => h1 (by rw [he]; exact hT1 11 (by omega))) (fun _ => ht)
    (fun h => absurd h (by omega))
  have := (heap_order H).2.2.2
  have := (heap_order H).2.1
  have := (heap_order H).2.2.1
  omega

/-- The fields `coreLocal`, `dPos`, `bran` and `lastB` of `BranchBSufOutKFBL` at the end of a run
of Branch B: the branch words of the levels are those of the model `X` after the exit, which is
the chain of `alg2PreResetState`. -/
theorem own_cells :
    Rcore.Local ∧ 0 < cfg.P.d ∧
    (∀ j < cfg.P.d, H.out.mem (tok.handle + 18 + (cfg.P.d + 1) + j) =
      (alg2PreResetState cfg model U
        (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
        (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.bran j) ∧
    H.out.mem (tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d) =
      (alg2PreResetState cfg model U
        (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
        (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.lastBran := by
  have hRep := H.start.rep0
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := hRep
  obtain ⟨hOwn, _, _, _, hT4, _⟩ := hTags
  have hdPos : 0 < cfg.P.d := H.start.modelInv.1.1
  have hBr (j : ℕ) (hj : j ≤ cfg.P.d) :
      H.out.mem (tok.handle + 18 + (cfg.P.d + 1) + j) =
        H.sX.mem (tok.handle + 18 + (cfg.P.d + 1) + j) := by
    have ht : tok.tag (tok.handle + 18 + (cfg.P.d + 1) + j) = 4 := by
      have := hT4 (cfg.P.d + 1 + j) (by omega)
      rwa [show tok.handle + 18 + (cfg.P.d + 1 + j) = tok.handle + 18 + (cfg.P.d + 1) + j by
        omega] at this
    have hlt : tok.handle + 18 + (cfg.P.d + 1) + j < uIntBuf :=
      H.start.footLt _ (Or.inl (hOwn _ (by rw [ht]; decide)))
    exact suffix_keep_low H hlt (by rw [ht]; decide) (by rw [ht]; decide)
  have hA : H.A.branchBase = tok.handle + 18 + (cfg.P.d + 1) := by rw [H.A_eq]; rfl
  have hMod := H.modelEq
  refine ⟨H.envA.coreLocal, hdPos, fun j hj => ?_, ?_⟩
  · rw [hBr j hj.le, ← hA, (H.exitOut.cells j hj).1, hMod, H.gVec_eq, H.lVec_eq]
  · rw [hBr _ le_rfl, ← hA, H.exitOut.lastB, hMod, H.gVec_eq, H.lVec_eq]


/-- A word of `[uIntBuf, heap + 1 + 12 d + 3 (d + 1) + 4)` keeps its value across the suffix of
Branch B: it lies off the tree, whose footprint is below `uIntBuf` or above that bound. -/
theorem suffix_keep_mid {a : ℕ} (h1 : uIntBuf ≤ a)
    (h2 : a < heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4) :
    H.out.mem a = H.sX.mem a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
  obtain ⟨hOwn, hT1, _⟩ := hTags
  obtain ⟨hU, hh0, hS1h, hFl, hX⟩ := heap_order H
  obtain ⟨_, _, _, _, _, _, _, _, _, hTreeFoot, _⟩ := H.pre
  obtain ⟨_, _, _, _, _, _, _, _, _, hFr, _⟩ := H.suf
  refine hFr a (by omega) (fun he => by
      have := H.start.footLt _ (Or.inl (hOwn _ (by rw [hT1 11 (by omega)]; decide))); omega)
    (fun h => absurd h (by omega)) (fun _ hf => ?_)
  rcases hTreeFoot a hf with h | h
  · have := H.start.footLt a (Or.inr (Or.inl h)); omega
  · omega


/-- The field `sel` of `BranchBSufOutKFBL`: the select base holds the first rebuilt level. -/
theorem own_sel : H.out.mem heap = H.fr := by
  have hU := (heap_order H).1
  have hA : H.A.selBase = heap := by rw [H.A_eq]; rfl
  have hs := H.exitOut.sel
  rw [hA] at hs
  rw [suffix_keep_mid H hU (by omega), hs]

/-- The handle words `tok.handle + 18 + j` (`j ≤ d`) keep their values across the suffix. -/
theorem suffix_keep_handle {j : ℕ} (hj : j ≤ cfg.P.d) :
    H.out.mem (tok.handle + 18 + j) = H.sX.mem (tok.handle + 18 + j) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
  obtain ⟨hOwn, _, _, _, hT4, _⟩ := hTags
  have ht : tok.tag (tok.handle + 18 + j) = 4 := hT4 j (by omega)
  exact suffix_keep_low H (H.start.footLt _ (Or.inl (hOwn _ (by rw [ht]; decide))))
    (by rw [ht]; decide) (by rw [ht]; decide)

/-- A word of the footprint of a core at the end of the exit keeps its value across the suffix:
it lies in the footprint of the core at the start (tag `21 + j`, below `uIntBuf`) or in the heap
of the loop and the exit, above the tree. -/
theorem suffix_keep_coreFoot {j a : ℕ} (hj : j < cfg.P.d)
    (ha : Rcore.foot (H.sX.mem (tok.handle + 18 + j)) (H.tokN j) a) :
    H.out.mem a = H.sX.mem a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags⟩ := H.start.rep0
  obtain ⟨hOwn, hT1, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT16, _, _, _, hT21⟩ := hTags
  obtain ⟨hU, hh0, hS1h, hFl, hX⟩ := heap_order H
  obtain ⟨_, _, _, _, _, _, _, _, _, hTreeFoot, _⟩ := H.pre
  obtain ⟨_, _, hF4, _⟩ := H.front
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hLFoot, _⟩ := H.loop
  obtain ⟨_, _, _, _, _, _, _, _, _, hFr, _⟩ := H.suf
  have hHB : H.A.handleBase = tok.handle + 18 := by rw [H.A_eq]; rfl
  have hCH : H.A.coreH j = tok.coreHandle j := by
    rw [H.A_eq]; show (if j < cfg.P.d then tok.coreHandle j else tok.termHandle) = _
    simp only [hj, ↓reduceIte]
  have hHigh (h1 : H.heap2 ≤ a) (h2 : a < H.sX.regs 4) : H.out.mem a = H.sX.mem a :=
    hFr a h2 (fun he => by
        have := H.start.footLt _ (Or.inl (hOwn _ (by rw [hT1 11 (by omega)]; decide))); omega)
      (fun h => absurd h (by omega)) (fun _ hf => by
        rcases hTreeFoot a hf with h | h
        · have := H.start.footLt a (Or.inr (Or.inl h)); omega
        · omega)
  rw [← hHB] at ha
  rcases (H.exitOut.reps j hj).2 a ha with hE | ⟨h1, h2⟩
  · rcases hLFoot j hj a hE with h0 | ⟨h1, h2⟩
    · rw [hCH] at h0
      have htag := hT21 j hj a h0
      have hlt := H.start.footLt a (Or.inr (Or.inr ⟨j, hj, h0⟩))
      exact suffix_keep_low H hlt (by rw [htag]; omega) (by rw [htag]; omega)
    · rw [hF4] at h1
      exact hHigh (by omega) (by omega)
  · exact hHigh (by omega) h2

/-- The fields `reps` and `coreDisj` of `BranchBSufOutKFBL`: the cores at the end of the exit
hold the levels of the chain of `alg2PreResetState`, with disjoint footprints, and the suffix keeps
their handles and footprints. -/
theorem own_cores :
    (∀ j < cfg.P.d, Rcore.rep (H.out.mem (tok.handle + 18 + j))
      (chainLevelOrdAbs (alg2PreResetState cfg model U
        (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
        (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain j)
      (H.tokN j) H.out.mem) ∧
    (∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ ≠ j₂ → ∀ a,
      Rcore.foot (H.out.mem (tok.handle + 18 + j₁)) (H.tokN j₁) a →
      ¬ Rcore.foot (H.out.mem (tok.handle + 18 + j₂)) (H.tokN j₂) a) := by
  have hHB : H.A.handleBase = tok.handle + 18 := by rw [H.A_eq]; rfl
  have hX : H.X = (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
    rw [H.modelEq, H.gVec_eq, H.lVec_eq]
  refine ⟨fun j hj => ?_, fun j₁ hj₁ j₂ hj₂ hne a => ?_⟩
  · rw [suffix_keep_handle H hj.le, ← hX]
    have hR := (H.exitOut.reps j hj).1
    rw [hHB] at hR
    exact (H.envA.coreLocal _ _ _ _ _ (fun a ha => (suffix_keep_coreFoot H hj ha).symm)).1 hR
  · rw [suffix_keep_handle H hj₁.le, suffix_keep_handle H hj₂.le]
    have hD := H.exitOut.disj j₁ hj₁ j₂ hj₂ hne a
    rw [hHB] at hD
    exact hD

end BranchBRunKFBL

end MinCostFlow.MinRatio
