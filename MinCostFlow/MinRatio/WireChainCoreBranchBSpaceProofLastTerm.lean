module

public import MinCostFlow.MinRatio.WireChainCoreBranchBSpaceProofLay
import MinCostFlow.MinRatio.WireChainCoreBranchBTermExitKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBStaticKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBFrontRepKFBL
import MinCostFlow.MinRatio.WireChainCoreSyncDefs

/-!
# Register preservation and terminal-exit handle location (`WireChainCoreBranchBSpaceProofLastTerm`)

Proves the shared helper facts for recovering the terminal-level handle location from
`BranchBRunKFBL` via `Runs.det`, together with the two terminal-exit cases:
* `branchB_loop_regs71_80_81`: `H.sE.regs 71 = 0`, `H.sE.regs 80 = oldPtrs`, `H.sE.regs 81 = newPtrs`,
  by proving that `wireBranchBLoopKFBL` never writes to registers `71`, `80`, or `81`.
* `branchB_XG0_eq`, `branchB_XG_m_le`, `branchB_prefixFrontLoop_room`: edge-count and room bounds
  needed to invoke the exit run lemmas.
* `branchBSpace_lastHandle_empty`: in the empty terminal exit (`H.fr = cfg.P.d + 1`),
  `H.sX.mem (H.A.handleBase + cfg.P.d) = H.A.coreH cfg.P.d`.
* `branchBSpace_lastHandle_term`: in the non-empty terminal exit (`H.fr = cfg.P.d`),
  `H.sE.regs 4 ≤ H.sX.mem (H.A.handleBase + cfg.P.d)`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

section RegPreservation

/-- A statement `s` never writes to register `r` as the target of `assign`, `rand`, or `call`. -/
private def StmtDoesNotWrite (r : ℕ) : Stmt → Prop
  | .nop => True
  | .assign r' _ => r' ≠ r
  | .store _ _ => True
  | .rand r' => r' ≠ r
  | .seq s t => StmtDoesNotWrite r s ∧ StmtDoesNotWrite r t
  | .cond _ s t => StmtDoesNotWrite r s ∧ StmtDoesNotWrite r t
  | .loop _ body => StmtDoesNotWrite r body
  | .call r' _ _ => r' ≠ r
  | .ret _ => True

private lemma exec_regs_of_notWrite {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} :
    ∀ (fuel : ℕ) (s : Stmt) (st st' : State) (o : Outcome) (c : ℕ),
      StmtDoesNotWrite r s →
      exec w p ω fuel s st = some (o, st', c) →
      st'.regs r = st.regs r
  | 0, _, _, _, _, _, _, h => by simp [exec] at h
  | fuel + 1, s, st, st', o, c, hnw, h => by
    cases s with
    | nop =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl, _⟩ := h; rfl
    | assign r' e =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, _⟩ := h
        exact Function.update_of_ne (Ne.symm hnw) v st.regs
    | store a e =>
      simp only [exec] at h
      cases ha : a.eval w st with
      | none => simp [ha] at h
      | some x =>
        cases he : e.eval w st with
        | none => simp [ha, he] at h
        | some v =>
          simp only [ha, he, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl, _⟩ := h; rfl
    | rand r' =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl, _⟩ := h
      exact Function.update_of_ne (Ne.symm hnw) _ st.regs
    | seq s₁ s₂ =>
      simp only [exec] at h
      cases h1 : exec w p ω fuel s₁ st with
      | none => simp [h1] at h
      | some res =>
        rcases res with ⟨o₁, st₁, c₁⟩
        cases o₁ with
        | returned v =>
          simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl, _⟩ := h
          exact exec_regs_of_notWrite fuel s₁ st st₁ (.returned v) c₁ hnw.1 h1
        | normal =>
          simp only [h1] at h
          cases h2 : exec w p ω fuel s₂ st₁ with
          | none => simp [h2] at h
          | some res₂ =>
            rcases res₂ with ⟨o₂, st₂, c₂⟩
            simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            exact (exec_regs_of_notWrite fuel s₂ st₁ st₂ o₂ c₂ hnw.2 h2).trans
              (exec_regs_of_notWrite fuel s₁ st st₁ .normal c₁ hnw.1 h1)
    | cond e s₁ s₂ =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h
        by_cases hv : v = 0
        · simp only [hv, ↓reduceIte] at h
          cases h2 : exec w p ω fuel s₂ st with
          | none => simp [h2] at h
          | some res =>
            rcases res with ⟨o₂, st₂, c₂⟩
            simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            exact exec_regs_of_notWrite fuel s₂ st st₂ o₂ c₂ hnw.2 h2
        · simp only [hv, ↓reduceIte] at h
          cases h1 : exec w p ω fuel s₁ st with
          | none => simp [h1] at h
          | some res =>
            rcases res with ⟨o₁, st₁, c₁⟩
            simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            exact exec_regs_of_notWrite fuel s₁ st st₁ o₁ c₁ hnw.1 h1
    | loop e body =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h
        by_cases hv : v = 0
        · simp only [hv, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl, _⟩ := h; rfl
        · simp only [hv, ↓reduceIte] at h
          cases h1 : exec w p ω fuel body st with
          | none => simp [h1] at h
          | some res =>
            rcases res with ⟨o₁, st₁, c₁⟩
            cases o₁ with
            | returned u =>
              simp only [h1, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨_, rfl, _⟩ := h
              exact exec_regs_of_notWrite fuel body st st₁ (.returned u) c₁ hnw h1
            | normal =>
              simp only [h1] at h
              cases h2 : exec w p ω fuel (.loop e body) st₁ with
              | none => simp [h2] at h
              | some res₂ =>
                rcases res₂ with ⟨o₂, st₂, c₂⟩
                simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨_, rfl, _⟩ := h
                exact (exec_regs_of_notWrite fuel (.loop e body) st₁ st₂ o₂ c₂ hnw h2).trans
                  (exec_regs_of_notWrite fuel body st st₁ .normal c₁ hnw h1)
    | call r' f args =>
      simp only [exec] at h
      cases ha : evalArgs w st args with
      | none => simp [ha] at h
      | some vs =>
        cases hf : p.procs[f]? with
        | none => simp [ha, hf] at h
        | some body =>
          cases hb : exec w p ω fuel body { st with regs := fun i => vs.getD i 0 } with
          | none => simp only [ha, hf, hb] at h; cases h
          | some res =>
            rcases res with ⟨o₁, st₁, c₁⟩
            simp only [ha, hf, hb, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl, _⟩ := h
            exact Function.update_of_ne (Ne.symm hnw) _ st.regs
    | ret e =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, _⟩ := h; rfl

private lemma runs_regs_of_notWrite {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {s : Stmt}
    {st st' : State} {o : Outcome} {c : ℕ}
    (hr : Runs w p ω s st o st' c) (hnw : StmtDoesNotWrite r s) :
    st'.regs r = st.regs r := by
  obtain ⟨fuel, hf⟩ := hr
  exact exec_regs_of_notWrite fuel s st st' o c hnw hf

private lemma loopKFBL_notWrite (updCore readLSF dgApply copyProc updLen slotProc : ℕ) {r : ℕ}
    (hr : 70 ≤ r) (h96 : r ≠ 96) (h99 : r ≠ 99) :
    StmtDoesNotWrite r (wireBranchBLoopKFBL updCore readLSF dgApply copyProc updLen slotProc) := by
  simp only [wireBranchBLoopKFBL, wireBranchBLoopBodyKFBL, wireBranchBStepKFBL,
    wireBranchBStepHeadKFBL, wireBranchBStepTailKFBL, wireBranchBStepTailFrontKFBL,
    wireBranchBCopyListsStmt, wireBranchBReadDescStmt, wireBranchBNextLenStmt,
    wireBranchBSlotStmt, ordCoreUpdateStmt, ordLoadBranchOutStmt, ordCoreReadLSFStmt,
    wireStretchDescCopyStmt, wireGuardCopyWordStmt, StmtDoesNotWrite]
  refine ⟨by omega, by omega, by omega, ⟨by omega, ⟨⟨⟨by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, trivial,
    ⟨by omega, by omega, by omega, by omega, by omega⟩, by omega⟩,
    ⟨⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega⟩,
      ⟨by omega, by omega, by omega, by omega, by omega, by omega,
        ⟨⟨by omega, ⟨trivial, trivial⟩⟩, ⟨by omega, ⟨trivial, trivial⟩⟩⟩⟩,
      ⟨⟨by omega, by omega⟩, trivial⟩⟩,
      ⟨by omega, by omega⟩⟩⟩, by omega⟩⟩⟩

private lemma collectTermForestStmt_mem_of_ne {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {st out : State} {c a : ℕ}
    (hr : Runs w p ω (collectTermForestStmt 81) st .normal out c)
    (hne : a ≠ st.regs 81 + (st.regs 75 - st.regs 71)) :
    out.mem a = st.mem a := by
  unfold collectTermForestStmt at hr
  rcases runs_seq_iff.mp hr with ⟨_, _, _, h, _⟩ | ⟨s1, _, _, r1, hr1, _⟩
  · exact Outcome.noConfusion h
  obtain ⟨v1, _, _, hs1, _⟩ := runs_assign_iff.mp r1
  subst hs1
  rcases runs_seq_iff.mp hr1 with ⟨_, _, _, h, _⟩ | ⟨s2, _, _, r2, hr2, _⟩
  · exact Outcome.noConfusion h
  obtain ⟨v2, _, _, hs2, _⟩ := runs_assign_iff.mp r2
  subst hs2
  rcases runs_seq_iff.mp hr2 with ⟨_, _, _, h, _⟩ | ⟨s3, _, _, r3, hr3, _⟩
  · exact Outcome.noConfusion h
  obtain ⟨v3, _, _, hs3, _⟩ := runs_assign_iff.mp r3
  subst hs3
  obtain ⟨addr, val, hAddr, _, _, hout, _⟩ := runs_store_iff.mp hr3
  have hr81 : (Function.update (Function.update (Function.update st.regs 10 v1) 11 v2) 12 v3) 81 =
      st.regs 81 := by simp [Function.update_of_ne]
  have hr75 : (Function.update (Function.update (Function.update st.regs 10 v1) 11 v2) 12 v3) 75 =
      st.regs 75 := by simp [Function.update_of_ne]
  have hr71 : (Function.update (Function.update (Function.update st.regs 10 v1) 11 v2) 12 v3) 71 =
      st.regs 71 := by simp [Function.update_of_ne]
  simp only [Expr.eval, BinOp.eval, hr81, hr75, hr71] at hAddr
  by_cases h1 : st.regs 75 - st.regs 71 < 2 ^ w
  · simp only [h1, ↓reduceIte] at hAddr
    by_cases h2 : st.regs 81 + (st.regs 75 - st.regs 71) < 2 ^ w
    · simp only [h2, ↓reduceIte, Option.some.injEq] at hAddr
      subst hout
      exact Function.update_of_ne (hAddr ▸ hne) val st.mem
    · simp only [h2, ↓reduceIte] at hAddr
      cases hAddr
  · simp only [h1, ↓reduceIte] at hAddr
    cases hAddr

end RegPreservation

section SharedAndTerminal

variable {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
    forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
    canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
    updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
    signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
    collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
  {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul : ℕ}
  {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
  {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
  {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
  {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
  {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
  {stepCap : ℕ → ℕ → ℕ}
  {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
  {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}

/-- Registers `71`, `80`, `81` keep their dispatch values across the prefix, front, and loop. -/
theorem branchB_loop_regs71_80_81
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    H.sE.regs 71 = 0 ∧ H.sE.regs 80 = heap + 1 + 12 * cfg.P.d ∧
      H.sE.regs 81 = heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) := by
  have hPreR := H.pre.2.2.1
  have hFrR := H.front.2.2.2.2
  have hLER := H.loop.2.2.2.2.2.2.2.2.2.1
  have hLRun := H.loop.1
  have hD := H.dispatch.2.2.1
  have hPres (r : ℕ) (h70 : 70 ≤ r) (h96 : r ≠ 96) (h97 : r ≠ 97) (h99 : r ≠ 99) :
      H.sE.regs r = H.st.regs r := by
    have h1 : H.sL.regs r = H.sE.regs r := hLER r (by omega) (by omega) (by omega) h99
    have h2 : H.sL.regs r = H.sF0.regs r :=
      runs_regs_of_notWrite hLRun (loopKFBL_notWrite _ _ _ _ _ _ h70 h96 h99)
    have h3 : H.sF0.regs r = H.sP.regs r :=
      hFrR r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h96 h97 h99
    have h4 : H.sP.regs r = H.st.regs r := hPreR r h70
    rw [← h1, h2, h3, h4]
  exact ⟨(hPres 71 (by omega) (by omega) (by omega) (by omega)).trans hD.2.2.1,
    (hPres 80 (by omega) (by omega) (by omega) (by omega)).trans
      hD.2.2.2.2.2.2.2.2.2.2.1,
    (hPres 81 (by omega) (by omega) (by omega) (by omega)).trans
      hD.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- In Branch B, level `0` is not rebuilt, so `H.X.G 0 = H.G1`. -/
theorem branchB_XG0_eq
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    H.X.G 0 = H.G1 := by
  rw [H.modelEq, H.G1_eq, H.Uint_eq]
  dsimp only [alg2PreResetState]
  rw [(Chain.Ordered.update_G0_ℓ cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain _ _ _).1,
    ite_eq_right H.start.noFire]

/-- Every level graph `H.X.G j` (`j ≤ cfg.P.d`) has at most `m` edges. -/
theorem branchB_XG_m_le
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    {j : ℕ} (hj : j ≤ cfg.P.d) :
    (H.X.G j).m ≤ m := by
  have hXEq : H.X = (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
    rw [H.modelEq, H.gVec_eq, H.lVec_eq]
  have hFacts : ShiftLoopLevelFacts cfg H.X := hXEq ▸ H.start.modelInvKFBL.2.1
  have hLe0 : (H.X.G j).m ≤ (H.X.G 0).m := hFacts.2.2.2 j hj
  rw [branchB_XG0_eq H, H.G1_eq, H.Uint_eq] at hLe0
  have hFresh0 : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt
      model.nextFresh := H.start.rep0.2.2.2.2.1
  have hTr := translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt
    model.intToExt model.nextFresh hFresh0 H.start.refresh.1
  have hFresh1 := hTr.2.1
  have hE1 : ((model.chain.G 0).applyBatch
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2).E =
      (model.extG.applyBatch U).E.image
        (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 := by
    rw [← hTr.1]; exact hFresh1.hE
  have hCard : ((model.chain.G 0).applyBatch
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2).m ≤
      model.extG.m := by
    unfold MGraph.m
    rw [hE1, H.start.refresh.2.1]
    exact Finset.card_image_le
  exact (hLe0.trans hCard).trans H.start.extM.le

/-- Heap room remaining at `H.sE.regs 4` for both the interior exit and the terminal exit. -/
theorem branchB_prefixFrontLoop_room
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    H.sE.regs 4 +
      (10 * cfg.P.d + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P 0 + 10 +
        (Finset.range cfg.P.d).sum levelSpace + lastSpace) + termUpdSpace < 2 ^ w := by
  have hhS1 : H.hS1 ≤ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 +
      (3 * U.length + U.length * wireTreeSyncEditSpace L) := by
    have := H.pre.2.2.2.2.1; omega
  have hheap2 : H.heap2 ≤ H.hS1 + 3 * L + U.length * wireRefreshOneSpace L :=
    H.pre.2.2.2.2.2.2.1
  have hsF0 : H.sF0.regs 4 = H.heap2 + (editsPtr - cfg.P.d - uIntBuf) := H.front.2.2.1
  have hbW : editsPtr - cfg.P.d - uIntBuf ≤ 4 * U.length + 1 := by
    have hEdits := branchBLevel0Edits_of_rep H.start.rep0 H.start.caps0 H.start.modelInv
      H.start.refresh
    have hLe := smallBatchAt_words_le_edgeOnly H.start.small hEdits.2.2.1
    have hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt
        model.nextFresh := H.start.rep0.2.2.2.2.1
    have hLen : (translateBatch model.extG model.extToInt model.intToExt
        model.nextFresh U).2.2.2.2.length = U.length :=
      (translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt model.intToExt
        model.nextFresh hFresh H.start.refresh.1).2.2.2.2.1
    rw [hLen] at hLe; exact hLe
  have hi₀Le : H.i₀ ≤ cfg.P.d := H.loop.2.2.1
  have hsE : H.sE.regs 4 ≤ H.sF0.regs 4 +
      (Finset.range cfg.P.d).sum (fun j => updStepSpace j U.length) := by
    have hL := H.loop.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hSub : Finset.Ico 0 H.i₀ ⊆ Finset.range cfg.P.d := fun j hj =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hj).2 hi₀Le)
    exact hL.trans (Nat.add_le_add_left (Finset.sum_le_sum_of_subset hSub) _)
  have hTot := H.envA.ops.spaceTotalBranchB U.length
  have hRoom := H.start.room
  omega

/-- Empty terminal exit (`H.curUE = []`): the terminal handle cell stays at `H.A.coreH cfg.P.d`. -/
theorem branchBSpace_lastHandle_empty
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hi₀ : H.i₀ = cfg.P.d) (hEmp : H.curUE = [])
    (hRun : Runs w p ω (wireBranchBTermKFBL (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
      collectTermForestStmt 81) H.sL .normal H.sX H.cX) :
    H.sX.mem (H.A.handleBase + cfg.P.d) = H.A.coreH cfg.P.d := by
  have hHeaps := branchBSpace_heaps H
  have hS := (branchBStatic_of_rep (heapFloor := H.heap2) H.start.rep0 H.start.meta0
    H.start.caps0 H.start.modelInv H.start.footLt hHeaps.1).1
  have hHB : H.A.handleBase = tok.handle + 18 := by rw [H.A_eq]; rfl
  have hSB : H.A.selBase = heap := by rw [H.A_eq]; rfl
  have hHBLt : H.A.handleBase + cfg.P.d < heap := by
    have := hS.hbLt; dsimp only [branchBAddrsOf] at this; rw [hHB]; omega
  obtain ⟨h71, _, h81⟩ := branchB_loop_regs71_80_81 H
  have hInv := H.loop.2.2.2.2.1
  have hLMem : H.sL.mem = H.sE.mem := H.loop.2.2.2.2.2.2.2.2.1
  have hLReg := H.loop.2.2.2.2.2.2.2.2.2.1
  have hR10 : H.sL.regs 10 = H.bE := (hLReg 10 (by decide) (by decide) (by decide) (by decide)).trans
    hInv.regs.2.1
  have hR72 : H.sL.regs 72 = heap := (hLReg 72 (by decide) (by decide) (by decide) (by decide)).trans
    (hInv.regs.2.2.2.2.2.1.trans hSB)
  have hR75 : H.sL.regs 75 = cfg.P.d :=
    (hLReg 75 (by decide) (by decide) (by decide) (by decide)).trans
      hInv.regs.2.2.2.2.2.2.2.2.1
  have hR71L : H.sL.regs 71 = 0 :=
    (hLReg 71 (by decide) (by decide) (by decide) (by decide)).trans h71
  have hR81L : H.sL.regs 81 = heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) :=
    (hLReg 81 (by decide) (by decide) (by decide) (by decide)).trans h81
  have hEmptyMem : H.sL.mem H.bE = 0 := by rw [hLMem, hInv.batchLen, hEmp]; rfl
  rcases runs_seq_iff.mp hRun with ⟨_, _, _, h, _⟩ | ⟨out1, _, _, r1, r2, _⟩
  · exact Outcome.noConfusion h
  have r1' := wireBranchBTermKFBL_runs_empty (w := w) (p := p) (ω := ω) (st := H.sL)
    (d := cfg.P.d) (selBase := heap) (curBatch := H.bE) (opCore 3) (opCore 2) coreLenProc
    (opCore 5) lastInit ⟨hR10, hR72, hR75⟩ hEmptyMem (by omega)
  have hout1 : out1 = { H.sL with mem := Function.update H.sL.mem heap (cfg.P.d + 1) } :=
    (Runs.det r1 r1').2.1
  subst hout1
  have hMemX := collectTermForestStmt_mem_of_ne r2 (a := H.A.handleBase + cfg.P.d) (by
    dsimp only; rw [hR81L, hR75, hR71L]; omega)
  rw [hMemX]
  dsimp only
  rw [Function.update_of_ne (by omega), hLMem]
  exact hInv.termCells.1

set_option maxHeartbeats 1600000 in
/-- Non-empty terminal exit (`H.curUE ≠ []`): the new terminal handle lies at or above
`H.sE.regs 4`. -/
theorem branchBSpace_lastHandle_term
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hi₀ : H.i₀ = cfg.P.d) (hneU : H.curUE ≠ [])
    (hX : H.X = (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g' 0 cfg.P.d
      H.chE H.curGE H.curUE H.curEncE).1)
    (hRun : Runs w p ω (wireBranchBTermKFBL (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
      collectTermForestStmt 81) H.sL .normal H.sX H.cX) :
    H.sE.regs 4 ≤ H.sX.mem (H.A.handleBase + cfg.P.d) := by
  have hHeaps := branchBSpace_heaps H
  have hS0 := (branchBStatic_of_rep (heapFloor := H.heap2) H.start.rep0 H.start.meta0
    H.start.caps0 H.start.modelInv H.start.footLt hHeaps.1).1
  have hS : BranchBStatic cfg.P.d L H.A.handle H.A.table H.A.handleBase H.A.branchBase
      H.A.lvlMTable H.A.levelMeta H.A.rcBase H.A.ucBase H.A.selBase (fun _ => vCap) (fun _ => eCap)
      H.A.gPtr0 H.A.lPtr0 H.A.coreH := by
    rw [H.A_eq]; exact hS0
  have hSB : H.A.selBase = heap := by rw [H.A_eq]; rfl
  have hHF : H.A.heapFloor = H.heap2 := by rw [H.A_eq]; rfl
  have hHBLt : H.A.handleBase + cfg.P.d < heap := by have := hS.hbLt; rw [hSB] at this; omega
  have hdPos : 0 < cfg.P.d := H.start.modelInv.1.1
  have hXEq : H.X = (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
    rw [H.modelEq, H.gVec_eq, H.lVec_eq]
  have hXGd : H.X.G cfg.P.d = H.curGE := by
    rw [hX]
    simp [Chain.Ordered.updateLoop, ite_eq_right hneU]
  have hFactsX : ShiftLoopLevelFacts cfg H.X := hXEq ▸ H.start.modelInvKFBL.2.1
  have hcurGm : H.curGE.m ≤ m := by rw [← hXGd]; exact branchB_XG_m_le H le_rfl
  have hcurGLvl : H.curGE.m ≤ levelM cfg.TP cfg.P cfg.P.d := by
    rw [← hXGd]; exact hXEq ▸ H.start.modelInvKFBL.2.2.2.2.2.2.2.2.2.1
  have hcurGn : H.curGE.n ≤ H.curGE.m + 1 := by rw [← hXGd]; exact hFactsX.1 cfg.P.d le_rfl
  have hcurGConn : ∀ u ∈ H.curGE.V, ∀ v ∈ H.curGE.V, H.curGE.Connected u v := by
    rw [← hXGd]; exact hXEq ▸ H.start.modelInvKFBL.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hLastImpl := H.envA.lastImpl H.curGE hcurGm hcurGLvl hcurGn hcurGConn
  have hLvlM : ∀ j < cfg.P.d, H.st0.lvlM j = levelM cfg.TP cfg.P j := fun j _ => by
    have h1 : H.st0.lvlM = model.chain.lvlM := by rw [H.st0_eq]
    rw [h1, H.start.modelInvKFBL.1.2.1]
  have hfrEq : H.fr = cfg.P.d := by
    rcases H.exitCase with hInt | hTerm | hEmpty
    · omega
    · exact hTerm.2.2.1
    · exact absurd hEmpty.2.1 hneU
  have hChEq := branchB_chain_lt_eq H (j := cfg.P.d - 1) (by omega)
  have hRotW : ordRotWords (chainLevelOrdAbs H.chE (cfg.P.d - 1)) (H.chE.bran (cfg.P.d - 1)) ≤
      1 + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P cfg.P.d := by
    have hRotEq : ordRotWords (chainLevelOrdAbs H.chE (cfg.P.d - 1)) (H.chE.bran (cfg.P.d - 1)) =
        ordRotWords (chainLevelOrdAbs H.X (cfg.P.d - 1)) (H.X.bran (cfg.P.d - 1)) := by
      unfold ordRotWords chainLevelOrdAbs; dsimp only; rw [hChEq.2.1, hChEq.2.2]
    rw [hRotEq]
    have h1 : ordRotWords (chainLevelOrdAbs H.X (cfg.P.d - 1)) (H.X.bran (cfg.P.d - 1)) ≤
        1 + 2 * (H.X.G (cfg.P.d - 1 + 1)).n + 2 * (H.X.G (cfg.P.d - 1 + 1)).m :=
      hXEq ▸ H.start.modelInvKFBL.2.2.2.2.1 (cfg.P.d - 1) (by omega)
    have hNLe : (H.X.G cfg.P.d).n ≤ cfg.N₀ := by
      have hN := hXEq ▸ H.start.modelInvKFBL.2.2.2.1 cfg.P.d le_rfl
      rw [hFactsX.2.2.1] at hN; exact hN
    have hMLe : (H.X.G cfg.P.d).m ≤ levelM cfg.TP cfg.P cfg.P.d := by
      rw [hXGd]; exact hcurGLvl
    rw [show cfg.P.d - 1 + 1 = cfg.P.d by omega] at h1
    omega
  have hRoom : H.sE.regs 4 + (1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
      levelM cfg.TP cfg.P cfg.P.d * wireCoreLenEdgeSpace
        (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) +
      (2 + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P cfg.P.d)) + lastSpace + 7 < 2 ^ w := by
    have hPFL := branchB_prefixFrontLoop_room H
    have hTD := H.envA.ops.termUpdSpaceDom
    omega
  have hInv : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt)
      (RL := LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
        (model.chain.G cfg.P.d).E) reembFn H.A
      (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j) H.ℓ' cfg.N₀
      (fun j => (H.C j).1) (fun j => (H.C j).2.1) (fun j => (H.C j).2.2) H.st0 tok.termTok
      cfg.P.d H.chE H.curGE H.curUE H.curEditsE H.oldOrdE H.sE H.tokE H.bE H.bWE H.eE H.eWE
      H.levelU H.levelUS H.D := hi₀ ▸ H.loop.2.2.2.2.1
  have hM : UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap)
      (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j) H.ℓ' H.g' 0 cfg.P.d H.chE
      H.curGE H.curUE H.curEncE H.oldOrdE := by
    have hM0 := H.loop.2.2.2.2.2.1
    rw [hi₀, Nat.sub_self] at hM0
    exact hM0
  rcases runs_seq_iff.mp hRun with ⟨_, _, _, h, _⟩ | ⟨out1, _, _, r1, r2, _⟩
  · exact Outcome.noConfusion h
  obtain ⟨out1', _, _, _, _, r1', _, _, _, _, hReg1, _, _, _, _, _, hTH1, _, _, _, _, _, _, _, _⟩ :=
    wireBranchBTermKFBL_runs_exit (lastAlloc := lastAlloc) (opLast := opLast) (ω := ω)
      (st := H.sL) (nextM := levelM cfg.TP cfg.P cfg.P.d) (lastMul := lastMul)
      (lastSpace := lastSpace)
      H.envB.loop
      (LastLevelProgram.lastLevelRepresentation_local tok.vcLast tok.ecLast 4 L P
        (model.chain.G cfg.P.d).E)
      hS (by rw [hSB, hHF]; exact hHeaps.2.1) rfl hLvlM hdPos hInv hM
      H.loop.2.2.2.2.2.2.2.2.1 H.loop.2.2.2.2.2.2.2.2.2.1 hneU H.envA.capLim H.envA.coreLenP
      hLastImpl H.envA.ops.lastSpaceDom H.envA.lW H.envA.pW H.envA.width hcurGLvl hRotW hRoom
  have hout1Eq : out1 = out1' := (Runs.det r1 r1').2.1
  subst hout1Eq
  obtain ⟨h71, _, h81⟩ := branchB_loop_regs71_80_81 H
  have hLReg := H.loop.2.2.2.2.2.2.2.2.2.1
  have hR71 : out1.regs 71 = 0 :=
    (hReg1 71 (by omega)).trans
      ((hLReg 71 (by decide) (by decide) (by decide) (by decide)).trans h71)
  have hR75 : out1.regs 75 = cfg.P.d :=
    (hReg1 75 (by omega)).trans
      ((hLReg 75 (by decide) (by decide) (by decide) (by decide)).trans
        hInv.regs.2.2.2.2.2.2.2.2.1)
  have hR81 : out1.regs 81 = heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) :=
    (hReg1 81 (by omega)).trans
      ((hLReg 81 (by decide) (by decide) (by decide) (by decide)).trans h81)
  have hMemX := collectTermForestStmt_mem_of_ne r2 (a := H.A.handleBase + cfg.P.d) (by
    rw [hR81, hR75, hR71]; omega)
  rw [hMemX]
  exact hTH1

end SharedAndTerminal

end MinCostFlow.MinRatio
