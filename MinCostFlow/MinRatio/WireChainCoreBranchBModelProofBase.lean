module

public import MinCostFlow.MinRatio.WireChainCoreBranchBModelGoalKFBL
import MinCostFlow.Chain.Ordered.UpdateTraceHelpers
import MinCostFlow.MinRatio.WireChainCoreBranchBModelKFBL
import MinCostFlow.MinRatio.WireChainCorePreAux
import MinCostFlow.MinRatio.PassReset

/-!
# Base model lemmas for `BranchBModelGoalKFBL` (`WireChainCoreBranchBModelProofBase`)

Proves the pure model fields and helpers of `BranchBModelFieldsKFBL` from `BranchBRunKFBL`:
* prefix preservation of `rebuildSuffix`, `algorithm1_rebuild`, and `updateLoop` (for `G`,
  `scState`, `bran`, `levelOrd`, `shiftCount`, `updCount d`, and `rebuildCount`);
* uniqueness of edge-only batches encoded by `DynSpanner.Program.BatchAt`
  (`batchAt_eq_of_isEdgeUpdate`);
* the fields `frPos`, `newForest`, `newSub`, `slotModel`, and `names` (from `frPos` and `link`);
* the Case 3 (`i₀ = d`, `curUE = []`, `fr = d + 1`) terminal graph equality
  `H.X.G cfg.P.d = model.chain.G cfg.P.d`, derived from `H.loop`'s `updateLoop` and step-data
  equations together with `LevelHistory.hOK.noHidden` at level `d - 1`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-! ### 1. Prefix preservation of `rebuildSuffix`, `algorithm1_rebuild`, and `updateLoop` -/

theorem rebuildSuffix_lt (T : SparseCoreRestartTool) (L : LastLevelTool) (P : ChainParams)
    (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ),
      let r := Chain.Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd
      (∀ j ≤ idx, r.1 j = G j) ∧
      (∀ j < idx, r.2.1 j = sc j ∧ r.2.2.1 j = bran j ∧ r.2.2.2.1 j = upd j) ∧
      (∀ j, idx + rem ≤ j → r.2.2.2.1 j = upd j)
  | 0, _, _, _, _, _, _, _, _ => ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl⟩
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd => by
    dsimp only [Chain.Ordered.rebuildSuffix]
    let Cp : TreeChain :=
      { d := P.d, k := P.k, G := G, lsfs := fun j => T.lsfs (sc j), bran := bran,
        S := fun j => T.S (sc j), emb := fun j => T.emb (sc j),
        lastK := 1, lastLSFs := fun _ => ⟨G idx, ⟨G idx, ∅⟩, fun _ => 1⟩, lastBran := 0 }
    let sc_i := T.initOrd P.k (lvlM idx) N₀ (G idx) (Cp.chainLen ℓ₀ idx) (Cp.chainGrad g₀ idx)
      (chainLevelOrd T G sc bran idx)
    have ih := rebuildSuffix_lt T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1)
      (fun j => if j = idx + 1 then T.S sc_i 0 else G j)
      (fun j => if j = idx then sc_i else sc j)
      (fun j => if j = idx then 0 else bran j)
      (fun j => if j = idx then 0 else upd j)
      (fun j => if j = idx then 0 else cEnc j)
      (fun j => if j = idx then 0 else cDec j)
      (fun j => if j = idx then 0 else cFwd j)
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · exact (ih.1 j (by omega)).trans (ite_eq_right (by omega))
    · obtain ⟨h1, h2, h3⟩ := ih.2.1 j (by omega)
      exact ⟨h1.trans (ite_eq_right (by omega)), h2.trans (ite_eq_right (by omega)),
        h3.trans (ite_eq_right (by omega))⟩
    · exact (ih.2.2 j (by omega)).trans (ite_eq_right (by omega))

theorem algorithm1_rebuild_lt (T : SparseCoreRestartTool) (L : LastLevelTool) (P : ChainParams)
    (st : ChainState T P) {i₀ : ℕ} (hi₀ : i₀ < P.d) (Gnew : MGraph) (extraEnc : ℕ) :
    let X := (Chain.Ordered.algorithm1_rebuild T L P st i₀ Gnew extraEnc).1
    (∀ j < i₀, X.G j = st.G j ∧ X.scState j = st.scState j ∧ X.bran j = st.bran j ∧
      X.levelOrd j = st.levelOrd j) ∧
    X.shiftCount = st.shiftCount ∧
    X.updCount P.d = st.updCount P.d ∧
    X.rebuildCount = fun j => if j = i₀ then st.rebuildCount i₀ + 1 else st.rebuildCount j := by
  dsimp only [Chain.Ordered.algorithm1_rebuild]
  rw [dite_eq_left_of_eq_true (eq_true hi₀)]
  have hS := rebuildSuffix_lt T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀
    (fun j => if j = i₀ then Gnew else st.G j) st.scState st.bran st.updCount st.curEnc
    st.curDecUpdates st.curFwd
  have hGlt : ∀ j < i₀, (Chain.Ordered.rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀
      (fun j => if j = i₀ then Gnew else st.G j) st.scState st.bran st.updCount st.curEnc
      st.curDecUpdates st.curFwd).1 j = st.G j := fun j hj => by
    rw [hS.1 j (by omega), ite_eq_right (by omega)]
  have hSclt : ∀ j < i₀, (Chain.Ordered.rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀
      (fun j => if j = i₀ then Gnew else st.G j) st.scState st.bran st.updCount st.curEnc
      st.curDecUpdates st.curFwd).2.1 j = st.scState j := fun j hj => (hS.2.1 j hj).1
  have hBrlt : ∀ j < i₀, (Chain.Ordered.rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀
      (fun j => if j = i₀ then Gnew else st.G j) st.scState st.bran st.updCount st.curEnc
      st.curDecUpdates st.curFwd).2.2.1 j = st.bran j := fun j hj => (hS.2.1 j hj).2.1
  refine ⟨fun j hj => ⟨hGlt j hj, hSclt j hj, hBrlt j hj, ?_⟩, rfl, ?_, rfl⟩
  · unfold ChainState.levelOrd chainLevelOrd
    dsimp only
    split_ifs with hj0
    · rw [hGlt 0 (by omega)]
    · rw [hSclt (j - 1) (by omega), hBrlt (j - 1) (by omega)]
  · exact hS.2.2 P.d (by omega)

theorem updateLoop_shiftCount_updCount_d (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEnc : ℕ),
      idx + rem = P.d →
      let X := (Chain.Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEnc).1
      X.shiftCount = st.shiftCount ∧ X.updCount P.d = st.updCount P.d
  | 0, _, st, _, curU, _, _ => by
    dsimp only [Chain.Ordered.updateLoop]
    split_ifs <;> exact ⟨rfl, rfl⟩
  | rem + 1, idx, st, curG, curU, curEnc, hSum => by
    dsimp only [Chain.Ordered.updateLoop]
    split_ifs with hT
    · have hR := algorithm1_rebuild_lt T L P
        { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
        (i₀ := idx) (by omega) (rebuildStartGraph idx curG) curEnc
      exact ⟨hR.2.1, hR.2.2.1⟩
    · refine ⟨(updateLoop_shiftCount_updCount_d T L TP P N₀ ℓ' g' rem (idx + 1) _ _ _ 0
          (by omega)).1, ?_⟩
      exact (updateLoop_shiftCount_updCount_d T L TP P N₀ ℓ' g' rem (idx + 1) _ _ _ 0
        (by omega)).2.trans (ite_eq_right (show P.d ≠ idx by omega))

theorem algorithm1_update_shiftCount_updCount_d (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P) (U : List Update)
    (g' ℓ' : ℕ → ℝ) :
    let X := (Chain.Ordered.algorithm1_update T L TP P N₀ st U g' ℓ').1
    X.shiftCount = st.shiftCount ∧ X.updCount P.d = st.updCount P.d := by
  exact updateLoop_shiftCount_updCount_d T L TP P N₀ ℓ' g' P.d 0 _ _ _ _ (by omega)

/-! ### 2. Uniqueness of edge-only batches encoded by `DynSpanner.Program.BatchAt` -/

private theorem batchBodyAt_eq_of_isEdgeUpdate {mem : ℕ → ℕ} :
    ∀ (U₁ U₂ : List Update) (a : ℕ) (G : MGraph) (w₁ w₂ : ℕ),
      U₁.length = U₂.length →
      (∀ u ∈ U₁, IsEdgeUpdate u) →
      BatchBodyAt mem a G U₁ w₁ →
      BatchBodyAt mem a G U₂ w₂ →
      U₁ = U₂
  | [], [], _, _, _, _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, hLen, _, _, _ => by simp at hLen
  | _ :: _, [], _, _, _, _, hLen, _, _, _ => by simp at hLen
  | u₁ :: us₁, u₂ :: us₂, a, G, w₁, w₂, hLen, hEdge, hB₁, hB₂ => by
    obtain ⟨len₁, _, hU₁, hR₁⟩ := hB₁
    obtain ⟨len₂, _, hU₂, hR₂⟩ := hB₂
    have hE₁ : IsEdgeUpdate u₁ := hEdge u₁ List.mem_cons_self
    have hLen' : us₁.length = us₂.length := by simpa using hLen
    have hEdge' : ∀ u ∈ us₁, IsEdgeUpdate u := fun u hu => hEdge u (List.mem_cons_of_mem _ hu)
    cases u₁ with
    | insert e₁ x₁ y₁ =>
      obtain ⟨rfl, hL₁⟩ := hU₁
      have h0 : mem a = 0 := by simpa using hL₁ 0 (by simp)
      have h1 : mem (a + 1) = e₁ := by simpa using hL₁ 1 (by simp)
      have h2 : mem (a + 2) = x₁ := by simpa using hL₁ 2 (by simp)
      have h3 : mem (a + 3) = y₁ := by simpa using hL₁ 3 (by simp)
      cases u₂ with
      | insert e₂ x₂ y₂ =>
        obtain ⟨rfl, hL₂⟩ := hU₂
        have he : e₁ = e₂ := h1.symm.trans (by simpa using hL₂ 1 (by simp))
        have hx : x₁ = x₂ := h2.symm.trans (by simpa using hL₂ 2 (by simp))
        have hy : y₁ = y₂ := h3.symm.trans (by simpa using hL₂ 3 (by simp))
        subst he hx hy
        congr 1
        exact batchBodyAt_eq_of_isEdgeUpdate us₁ us₂ (a + 4) (G.applyUpdate (.insert e₁ x₁ y₁))
          (w₁ - 4) (w₂ - 4) hLen' hEdge' hR₁ hR₂
      | delete e₂ =>
        obtain ⟨_, hL₂⟩ := hU₂
        have h0' : mem a = 1 := by simpa using hL₂ 0 (by simp)
        omega
      | split v v' St Sh =>
        rcases hU₂ with ⟨_, _, _, _, _, _, _, hL₂⟩ | ⟨_, _, _, _, _, _, _, hL₂⟩
        · have h0' : mem a = 2 := by simpa using hL₂ 0 (by simp)
          omega
        · have h0' : mem a = 3 := by simpa using hL₂ 0 (by simp)
          omega
    | delete e₁ =>
      obtain ⟨rfl, hL₁⟩ := hU₁
      have h0 : mem a = 1 := by simpa using hL₁ 0 (by simp)
      have h1 : mem (a + 1) = e₁ := by simpa using hL₁ 1 (by simp)
      cases u₂ with
      | insert e₂ x₂ y₂ =>
        obtain ⟨_, hL₂⟩ := hU₂
        have h0' : mem a = 0 := by simpa using hL₂ 0 (by simp)
        omega
      | delete e₂ =>
        obtain ⟨rfl, hL₂⟩ := hU₂
        have he : e₁ = e₂ := h1.symm.trans (by simpa using hL₂ 1 (by simp))
        subst he
        congr 1
        exact batchBodyAt_eq_of_isEdgeUpdate us₁ us₂ (a + 2) (G.applyUpdate (.delete e₁))
          (w₁ - 2) (w₂ - 2) hLen' hEdge' hR₁ hR₂
      | split v v' St Sh =>
        rcases hU₂ with ⟨_, _, _, _, _, _, _, hL₂⟩ | ⟨_, _, _, _, _, _, _, hL₂⟩
        · have h0' : mem a = 2 := by simpa using hL₂ 0 (by simp)
          omega
        · have h0' : mem a = 3 := by simpa using hL₂ 0 (by simp)
          omega
    | split _ _ _ _ => exact hE₁.elim

/-- Two `DynSpanner.Program.BatchAt` encodings at the same memory address represent the same list
of updates whenever the first batch contains only edge updates. -/
theorem batchAt_eq_of_isEdgeUpdate {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U₁ U₂ : List Update}
    {w₁ w₂ : ℕ} (hEdge : ∀ u ∈ U₁, IsEdgeUpdate u)
    (h₁ : DynSpanner.Program.BatchAt mem a G U₁ w₁)
    (h₂ : DynSpanner.Program.BatchAt mem a G U₂ w₂) : U₁ = U₂ :=
  batchBodyAt_eq_of_isEdgeUpdate U₁ U₂ (a + 1) G (w₁ - 1) (w₂ - 1)
    (h₁.2.1.symm.trans h₂.2.1) hEdge h₁.2.2 h₂.2.2

/-! ### 3. Direct model fields of `BranchBModelFieldsKFBL` -/

section RunFields

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

theorem branchBModel_frPos
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    0 < H.fr := by
  have hdPos : 0 < cfg.P.d := H.start.modelInv.1.1
  rcases H.exitCase with h1 | h2 | h3
  · omega
  · omega
  · omega

theorem branchBModel_min_fr_d
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    min H.fr cfg.P.d = H.i₀ := by
  rcases H.exitCase with h1 | h2 | h3 <;> omega

theorem branchBModel_X_lt
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    {j : ℕ} (hj : j < H.i₀) :
    H.X.G j = H.chE.G j ∧ H.X.scState j = H.chE.scState j ∧ H.X.bran j = H.chE.bran j ∧
    H.X.levelOrd j = H.chE.levelOrd j := by
  rcases H.exitCase with h1 | h2 | h3
  · obtain ⟨_, hiLt, _, _, _, hXeq, _⟩ := h1
    have hR := algorithm1_rebuild_lt cfg.T cfg.L cfg.P { H.chE with ℓ := H.ℓ', g := H.g' }
      hiLt H.curGE H.curEncE
    rw [hXeq]
    exact hR.1 j hj
  · obtain ⟨hiEq, hne, _, _, _, hXeq, _⟩ := h2
    have hG : ∀ k < cfg.P.d, H.X.G k = H.chE.G k := fun k hk => by
      rw [hXeq]; simp [Chain.Ordered.updateLoop, hne, hk.ne]
    have hSc : H.X.scState = H.chE.scState := by
      rw [hXeq]; simp [Chain.Ordered.updateLoop, hne]
    have hBr : H.X.bran = H.chE.bran := by
      rw [hXeq]; simp [Chain.Ordered.updateLoop, hne]
    refine ⟨hG j (by omega), congrFun hSc j, congrFun hBr j, ?_⟩
    unfold ChainState.levelOrd chainLevelOrd
    split_ifs with hj0
    · rw [hG 0 (by omega)]
    · rw [hSc, hBr]
  · obtain ⟨hiEq, hemp, _, _, _, hXeq, _⟩ := h3
    have hG : ∀ k < cfg.P.d, H.X.G k = H.chE.G k := fun k hk => by
      rw [hXeq]; simp [Chain.Ordered.updateLoop, hemp, hk.ne]
    have hSc : H.X.scState = H.chE.scState := by
      rw [hXeq]; simp [Chain.Ordered.updateLoop, hemp]
    have hBr : H.X.bran = H.chE.bran := by
      rw [hXeq]; simp [Chain.Ordered.updateLoop, hemp]
    refine ⟨hG j (by omega), congrFun hSc j, congrFun hBr j, ?_⟩
    unfold ChainState.levelOrd chainLevelOrd
    split_ifs with hj0
    · rw [hG 0 (by omega)]
    · rw [hSc, hBr]

theorem branchBModel_newForest
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.toTreeChain.chainTree.IsForest :=
  H.start.modelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem branchBModel_newSub
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.toTreeChain.chainTree.E ⊆
    ((alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.G 0).E :=
  H.start.modelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem branchBModel_slotModel
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
    ∀ j < min H.fr cfg.P.d,
      (H.D j).uG = coreBatchTouchedEdges (H.levelU j) ∧
      (H.D j).uS = coreBatchTouchedEdges (H.levelUS j) ∧
      (H.D j).fDel.Nodup ∧
      (H.D j).fDel.toFinset = (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.E \
        (cfg.T.lsfs ((alg2PreResetState cfg model U gVec lVec).chain.scState j)
          ((alg2PreResetState cfg model U gVec lVec).chain.bran j)).F.F.E ∧
      (H.D j).reemb = reembFn (model.chain.scState j) (H.levelU j)
        ((alg2PreResetState cfg model U gVec lVec).chain.levelOrd j) (model.chain.bran j) ∧
      BatchWithinCaps vCap eCap (H.levelU j) := by
  intro gVec lVec j hj
  have hj' : j < H.i₀ := by rw [← branchBModel_min_fr_d H]; exact hj
  have hMod : (alg2PreResetState cfg model U gVec lVec).chain = H.X := by
    dsimp only [gVec, lVec]
    rw [← H.gVec_eq, ← H.lVec_eq]; exact H.modelEq.symm
  have hI := H.loop.2.2.2.2.1.slotModel j hj'
  have hXlt := branchBModel_X_lt H hj'
  have hSc0 : H.st0.scState j = model.chain.scState j := by rw [H.st0_eq]
  have hBr0 : H.st0.bran j = model.chain.bran j := by rw [H.st0_eq]
  rw [hMod, hXlt.2.1, hXlt.2.2.1, hXlt.2.2.2]
  rw [hSc0, hBr0] at hI
  exact ⟨hI.1, hI.2.1, hI.2.2.1, hI.2.2.2.1, hI.2.2.2.2.1, hI.2.2.2.2.2.1⟩

theorem branchBModel_names_of_link
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hLink : UpdateCoreLevelLink model.chain
      (alg2PreResetState cfg model U
        (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
        (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain
      H.fr H.levelU H.levelUS) :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let modelPre := alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)
    modelPre.extToInt = tr.2.1 ∧ modelPre.intToExt = tr.2.2.1 ∧ modelPre.nextFresh = tr.2.2.2.1 := by
  intro tr modelPre
  have hFrPos := branchBModel_frPos H
  have hNe0 : firstRebuiltLevel cfg.P.d model.chain.rebuildCount modelPre.chain.rebuildCount ≠
      some 0 := by
    by_cases hlt : H.fr < cfg.P.d
    · rw [hLink.2.1 hlt]
      intro h; exact absurd (Option.some.inj h) (by omega)
    · rw [hLink.2.2.1 (by omega)]
      simp
  have hRen : level0Rebuilt cfg.P.d model.chain.rebuildCount modelPre.chain.rebuildCount = false := by
    unfold level0Rebuilt
    exact decide_eq_false hNe0
  change level0E2I (level0Rebuilt cfg.P.d model.chain.rebuildCount modelPre.chain.rebuildCount)
      ((model.chain.G 0).applyBatch tr.2.2.2.2) tr.2.1 = tr.2.1 ∧
    level0I2E (level0Rebuilt cfg.P.d model.chain.rebuildCount modelPre.chain.rebuildCount)
      ((model.chain.G 0).applyBatch tr.2.2.2.2) tr.2.2.1 = tr.2.2.1 ∧
    level0NF (level0Rebuilt cfg.P.d model.chain.rebuildCount modelPre.chain.rebuildCount)
      ((model.chain.G 0).applyBatch tr.2.2.2.2) tr.2.2.2.1 = tr.2.2.2.1
  rw [hRen]
  exact ⟨rfl, rfl, rfl⟩

/-! ### 4. Case 3 (`i₀ = d`, `curUE = []`): `H.X.G d = model.chain.G d` -/

/-- Walking `updateLoop` across `rem > 0` non-rebuilding levels from `idx` to `d - 1` produces
a valid 1-step extension of the level-`d - 1` history, giving `X.G d = (origCh.G d).applyBatch []`
when the forwarded batch at `d - 1` has length `0`. -/
private theorem updateLoop_noFire_last_G {w L P wordExp stretchPrec : ℕ} {cfg : Alg2Config}
    {vcOf ecOf : ℕ → ℕ} {ℓ' g' : ℕ → ℝ} {origCh : ChainState cfg.T cfg.P}
    (hInv : Chain.Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ origCh) :
    ∀ (rem idx : ℕ) (st : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update)
      (curEnc : ℕ) (oldOrd : ℕ → List End),
      0 < rem →
      idx + rem = cfg.P.d →
      st.N₀ = cfg.N₀ →
      st.lvlM = levelM cfg.TP cfg.P →
      st.bran = origCh.bran →
      st.rebuildCount = origCh.rebuildCount →
      (∀ j, idx ≤ j → st.G j = origCh.G j ∧ st.scState j = origCh.scState j ∧
        st.updCount j = origCh.updCount j) →
      oldOrd = origCh.levelOrd idx →
      ((Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' rem idx st curG curU
          curEnc).1).rebuildCount = origCh.rebuildCount →
      UpdateLoopModelInv w L P wordExp stretchPrec vcOf ecOf
        (fun j => origCh.toTreeChain.chainLen origCh.ℓ j) ℓ' g' rem idx st curG curU curEnc
        oldOrd →
      (∀ e ∈ curG.E, e ∈ (origCh.G idx).E → (∀ u ∈ curU, ¬ u.Inserts e) →
        ({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } :
          TreeChain).chainLen ℓ' idx e = origCh.toTreeChain.chainLen origCh.ℓ idx e) →
      (branchBStepData cfg ℓ' g' rem idx st curG curU curEnc (cfg.P.d - 1)).2.2 = 0 →
      ((Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' rem idx st curG curU
          curEnc).1).G cfg.P.d = origCh.G cfg.P.d
  | 0, _, _, _, _, _, _, hRem, _, _, _, _, _, _, _, _, _, _, _ => absurd hRem (Nat.lt_irrefl _)
  | rem + 1, idx, st, curG, curU, curEnc, oldOrd, _, hSum, hN0, hLvlM, hBr, hReb, hGe, hOrd,
      hEndReb, hM, hLenStab, hStepLen => by
    have hIdxLt : idx < cfg.P.d := by omega
    -- Threshold test cannot fire at `idx`, else `rebuildCount idx` would increase by 1
    have hNotOver : ¬ intRebuildThreshold cfg.P cfg.N₀ idx < st.updCount idx + curU.length := by
      intro hOver
      have hUL := hEndReb
      simp only [Chain.Ordered.updateLoop, ite_eq_left hOver] at hUL
      have hR := algorithm1_rebuild_lt cfg.T cfg.L cfg.P
        { st with ℓ := rebuildStartFn idx curG ℓ', g := rebuildStartFn idx curG g' }
        hIdxLt (rebuildStartGraph idx curG) curEnc
      have hAt := congrFun (hR.2.2.2.symm.trans hUL) idx
      simp only [↓reduceIte] at hAt
      rw [hReb] at hAt
      omega
    have hNotOver' : ¬ intRebuildThreshold cfg.P st.N₀ idx < st.updCount idx + curU.length := by
      rw [hN0]; exact hNotOver
    obtain ⟨_, hBValid, _, hCurGEq, _, hTail⟩ := hM
    rw [ite_eq_right hNotOver'] at hTail
    obtain ⟨_, hOrdB, hThr, _, hℓPos, hNextSpec, hNextM⟩ := hTail
    set Cp : TreeChain := { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
    set ℓi := Cp.chainLen ℓ' idx
    set gi := Cp.chainGrad g' idx
    set newOrd := chainLevelOrd cfg.T (fun j => if j = idx then curG else st.G j)
      st.scState st.bran idx
    set upd := cfg.T.updateOrd (st.scState idx) curU ℓi gi newOrd
    set sc' := upd.1
    set nextG := cfg.T.S sc' (st.bran idx)
    set nextU := upd.2 (st.bran idx)
    cases rem with
    | zero =>
      have hIdxEq : idx = cfg.P.d - 1 := by omega
      have hStepLen' : nextU.length = 0 := by
        simpa only [branchBStepData, ite_eq_right hNotOver', branchBStepNext, ite_eq_left hIdxEq.symm]
          using hStepLen
      have hNextUEmpty : nextU = [] := List.eq_nil_of_length_eq_zero hStepLen'
      have hEndG : ((Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' 1 idx st curG
          curU curEnc).1).G cfg.P.d = nextG := by
        unfold Chain.Ordered.updateLoop
        rw [ite_eq_right hNotOver]
        dsimp only
        change ((Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' 0 (idx + 1) _
          nextG nextU 0).1).G cfg.P.d = nextG
        simp only [Chain.Ordered.updateLoop, hNextUEmpty, ↓reduceIte]
      rw [hEndG]
      -- Extend `LevelHistory` at `idx` by 1 step and apply `ToolOKAt.noHidden`
      obtain ⟨Hh⟩ := hInv.hHist idx hIdxLt
      have hStG : st.G idx = origCh.G idx := (hGe idx le_rfl).1
      have hStSc : st.scState idx = origCh.scState idx := (hGe idx le_rfl).2.1
      have hStUpd : st.updCount idx = origCh.updCount idx := (hGe idx le_rfl).2.2
      have hStBr : st.bran idx = origCh.bran idx := congrFun hBr idx
      let D' := extendDyn Hh.D Hh.len curU curG ℓi gi
      let ord' := U3.extendOrd Hh.ord Hh.len newOrd
      let restarts' : ℕ → List ℕ := fun r => if r ≤ Hh.len then Hh.restarts r else []
      have hStepG : curG = (Hh.D.G Hh.len).applyBatch curU := by
        rw [Hh.hEndG, ← hStG]; exact hCurGEq
      have hD'Valid : D'.IsValid (Hh.len + 1) := by
        intro s hs1 hs2
        by_cases hsl : s ≤ Hh.len
        · have hs' : s - 1 ≤ Hh.len := by omega
          simpa only [D', extendDyn, hsl, hs', ↓reduceIte] using Hh.hD s hs1 hsl
        · have hseq : s = Hh.len + 1 := by omega
          subst hseq
          have hns : ¬ (Hh.len + 1 ≤ Hh.len) := by omega
          simp only [D', extendDyn, hns, le_rfl, Nat.add_sub_cancel, ↓reduceIte]
          exact ⟨by rw [Hh.hEndG, ← hStG]; exact hBValid, hStepG⟩
      have hLenStable' : LengthsStable D' (Hh.len + 1) := by
        intro s hs1 hs2 e he1 he2 hNoIns
        by_cases hsl : s ≤ Hh.len
        · have hs' : s - 1 ≤ Hh.len := by omega
          simp only [D', extendDyn, hsl, hs', ↓reduceIte] at he1 he2 hNoIns ⊢
          exact Hh.hLen s hs1 hsl e he1 he2 hNoIns
        · have hseq : s = Hh.len + 1 := by omega
          subst hseq
          have hns : ¬ (Hh.len + 1 ≤ Hh.len) := by omega
          simp only [D', extendDyn, hns, le_rfl, Nat.add_sub_cancel, ↓reduceIte] at he1 he2 hNoIns ⊢
          rw [Hh.hEndG] at he2
          rw [Hh.hEndℓ e he2]
          exact hLenStab e he1 he2 hNoIns
      have hℓPos' : ∀ s ≤ Hh.len + 1, ∀ e ∈ (D'.G s).E, 0 < D'.ℓ s e := by
        intro s hs e he
        by_cases hsl : s ≤ Hh.len
        · simp only [D', extendDyn, hsl, ↓reduceIte] at he ⊢
          exact Hh.hℓPos s hsl e he
        · simp only [D', extendDyn, hsl, ↓reduceIte] at he ⊢
          exact hℓPos e he
      have hOrd' : OrderedUpTo D' (Hh.len + 1) 2 ord' := by
        obtain ⟨ρPrev, ρNew, hρ1, hρ2, hRB⟩ := hOrdB
        have hEq1 : st.G idx = Hh.D.G Hh.len := hStG.trans Hh.hEndG.symm
        have hEq2 : (st.G idx).applyBatch curU = curG := hCurGEq.symm
        refine U3.orderedUpTo_extend_step Hh.hOrd curU curG ℓi gi newOrd hStepG
          ⟨hEq1 ▸ ρPrev, hEq2 ▸ ρNew, ?_, ?_, ?_⟩
        · rw [U3.rotation_cast_order, hρ1, hOrd, Hh.hEndOrd]
        · rw [U3.rotation_cast_order, hρ2]
        · exact U3.rotationBatch_cast hEq1 rfl rfl hStepG
            (U3.rotation_cast_order hEq1 ρPrev).symm
            (U3.rotation_cast_order hEq2 ρNew).symm hRB
      have hRestLt' : ∀ r ≤ Hh.len + 1, ∀ j ∈ restarts' r, j < cfg.P.k := by
        intro r _ j hj
        dsimp only [restarts'] at hj
        split_ifs at hj with hr
        · exact Hh.hRestartsLt r hr j hj
        · cases hj
      have hSumUpd : (Finset.Icc 1 (Hh.len + 1)).sum (fun s => (D'.U s).length) =
          st.updCount idx + curU.length := by
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hPref : (Finset.Icc 1 Hh.len).sum (fun s => (D'.U s).length) =
            (Finset.Icc 1 Hh.len).sum (fun s => (Hh.D.U s).length) := by
          refine Finset.sum_congr rfl fun s hs => ?_
          have hsl : s ≤ Hh.len := (Finset.mem_Icc.mp hs).2
          simp [D', extendDyn, hsl]
        have hLast : (D'.U (Hh.len + 1)).length = curU.length := by
          simp [D', extendDyn]
        rw [hPref, hLast, Hh.hUpd, hStUpd]
      have hThr' : (((Finset.Icc 1 (Hh.len + 1)).sum fun s => (D'.U s).length : ℕ) : ℝ) ≤
          SparseCoreTool.updateThreshold cfg.P.k (levelM cfg.TP cfg.P idx) cfg.N₀ := by
        rw [hSumUpd]
        have hLvlIdx : st.lvlM idx = levelM cfg.TP cfg.P idx := congrFun hLvlM idx
        rw [← hLvlIdx, ← hN0]
        exact hThr
      have hSpec := Hh.hOK.noHidden cfg.P.k (Hh.len + 1) (levelM cfg.TP cfg.P idx) cfg.N₀
        D' ord' restarts' cfg.P.hk (by simpa [D', extendDyn] using Hh.hG0) hD'Valid hLenStable'
        hℓPos' hOrd' (by simpa [D', extendDyn] using Hh.hInitMBound)
        (by simpa [D', extendDyn] using Hh.hInitNBound) hRestLt' hThr'
        ⟨rfl, rfl, rfl, by simp [D', extendDyn], by simp [D', extendDyn]⟩
      have hStepSpec := hSpec.2.1 (Hh.len + 1) (by omega) le_rfl (origCh.bran idx)
        (hInv.hBran idx hIdxLt)
      have hPostLen : cfg.T.runOrdAfterRestarts cfg.P.k (levelM cfg.TP cfg.P idx) cfg.N₀
          D' ord' restarts' Hh.len = st.scState idx := by
        dsimp only [D', ord', restarts']
        rw [runOrdAfterRestarts_extendDyn_prefix cfg.T cfg.P.k (levelM cfg.TP cfg.P idx) cfg.N₀
          Hh.D Hh.ord Hh.restarts Hh.len curU curG ℓi gi newOrd Hh.len le_rfl, ← Hh.hRun, hStSc]
      have hPreNext : cfg.T.runOrdAfterUpdate cfg.P.k (levelM cfg.TP cfg.P idx) cfg.N₀
          D' ord' restarts' (Hh.len + 1) = upd := by
        rw [SparseCoreRestartTool.runOrdAfterUpdate_succ, hPostLen]
        simp [D', extendDyn, ord', U3.extendOrd, upd]
      have hEqS := hStepSpec.2.2.2.2
      simp only [Nat.add_sub_cancel, hPostLen, hPreNext] at hEqS
      have hGSucc : origCh.G cfg.P.d = cfg.T.S (st.scState idx) (origCh.bran idx) := by
        rw [show cfg.P.d = idx + 1 by omega, hStSc]
        exact hInv.hGSucc idx hIdxLt
      calc nextG = cfg.T.S upd.1 (origCh.bran idx) := by dsimp only [nextG, sc']; rw [hStBr]
        _ = (cfg.T.S (st.scState idx) (origCh.bran idx)).applyBatch (upd.2 (origCh.bran idx)) := hEqS
        _ = (origCh.G cfg.P.d).applyBatch nextU := by dsimp only [nextU]; rw [← hGSucc, ← hStBr]
        _ = origCh.G cfg.P.d := by rw [hNextUEmpty]; rfl
    | succ rem' =>
      have hIdx1Lt : idx + 1 < cfg.P.d := by omega
      have hNeLast : cfg.P.d - 1 ≠ idx := by omega
      have hStepLen' : (branchBStepData cfg ℓ' g' (rem' + 1) (idx + 1)
          (branchBStepNext cfg ℓ' g' idx st curG curU curEnc).1 nextG nextU 0 (cfg.P.d - 1)).2.2 =
          0 := by
        simpa only [branchBStepData, ite_eq_right hNotOver', ite_eq_right hNeLast, branchBStepNext]
          using hStepLen
      have hEndReb' : ((Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' (rem' + 1)
          (idx + 1) (branchBStepNext cfg ℓ' g' idx st curG curU curEnc).1 nextG nextU 0).1).rebuildCount =
          origCh.rebuildCount := by
        simpa only [Chain.Ordered.updateLoop, ite_eq_right hNotOver, branchBStepNext] using hEndReb
      have hEndG : ((Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' (rem' + 2) idx
          st curG curU curEnc).1).G cfg.P.d =
          ((Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ' g' (rem' + 1) (idx + 1)
            (branchBStepNext cfg ℓ' g' idx st curG curU curEnc).1 nextG nextU 0).1).G cfg.P.d := by
        unfold Chain.Ordered.updateLoop
        rw [ite_eq_right hNotOver]
        rfl
      rw [hEndG]
      obtain ⟨_, _, hLenCore⟩ := hNextSpec hIdx1Lt
      refine updateLoop_noFire_last_G hInv (rem' + 1) (idx + 1)
        (branchBStepNext cfg ℓ' g' idx st curG curU curEnc).1 nextG nextU 0
        (cfg.T.rot (st.scState idx) (st.bran idx)) (by omega) (by omega) hN0 hLvlM hBr hReb
        (fun j hj => by
          have hne : j ≠ idx := by omega
          simp only [branchBStepNext, ite_eq_right hne]
          exact hGe j (by omega))
        (by
          unfold ChainState.levelOrd chainLevelOrd
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
          rw [(hGe idx le_rfl).2.1, congrFun hBr idx])
        hEndReb' hNextM ?_ hStepLen'
      intro e heNext _ hNoIns
      have hC := (hLenCore e heNext hNoIns).2
      have hAct : ({ (branchBStepNext cfg ℓ' g' idx st curG curU curEnc).1.toTreeChain with
          G := fun j => if j = idx + 1 then nextG else
            (branchBStepNext cfg ℓ' g' idx st curG curU curEnc).1.G j } :
          TreeChain).activeLSF idx = cfg.T.lsfs sc' (st.bran idx) := by
        simp [TreeChain.activeLSF, ChainState.toTreeChain, branchBStepNext, hIdxLt, sc', upd,
          newOrd, ℓi, gi, Cp]
      have hLenPrev : ({ (branchBStepNext cfg ℓ' g' idx st curG curU curEnc).1.toTreeChain with
          G := fun j => if j = idx + 1 then nextG else
            (branchBStepNext cfg ℓ' g' idx st curG curU curEnc).1.G j } :
          TreeChain).chainLen ℓ' idx = ℓi := by
        refine chainLen_congr_lt _ _ _ _ fun j hj => ?_
        have hne : j ≠ idx := by omega
        have hlt : j < cfg.P.d := by omega
        simp [TreeChain.activeLSF, ChainState.toTreeChain, branchBStepNext, hlt, hne, Cp]
      show coreLen _ _ e = _
      rw [hAct, hLenPrev]
      exact hC

/-- In Case 3 (`i₀ = d`, `curUE = []`, `fr = d + 1`), the terminal graph of the new chain equals
the old terminal graph `model.chain.G d`. -/
theorem branchBModel_case3_Gd_eq
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hiD : H.i₀ = cfg.P.d) (hEmpty : H.curUE = []) :
    H.X.G cfg.P.d = model.chain.G cfg.P.d := by
  have hdPos : 0 < cfg.P.d := H.start.modelInv.1.1
  have hInv : Chain.Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ model.chain :=
    H.start.shiftInv.1
  -- Extract the `updateLoop` equation from `H.loop` and `H.exitCase`
  have hUL : (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g' cfg.P.d 0 H.st0
      H.G1 H.Uint ((model.chain.G 0).batchEnc H.Uint)).1 = H.X := by
    have hL := H.loop.2.2.2.2.2.2.2.1
    rcases H.exitCase with h1 | h2 | h3
    · omega
    · exact absurd hEmpty h2.2.1
    · rw [hiD, Nat.sub_self] at hL
      exact hL.trans h3.2.2.2.2.2.1.symm
  have hRebEq : H.X.rebuildCount = model.chain.rebuildCount := by
    rcases H.exitCase with h1 | h2 | h3
    · omega
    · exact absurd hEmpty h2.2.1
    · rw [h3.2.2.2.2.2.1]
      simp only [Chain.Ordered.updateLoop, hEmpty, ↓reduceIte]
      rw [H.loop.2.2.2.2.1.modelFrame.2.2.2.2.2.2.2, H.st0_eq]
  have hStepLen : (branchBStepData cfg H.ℓ' H.g' cfg.P.d 0 H.st0 H.G1 H.Uint
      ((model.chain.G 0).batchEnc H.Uint) (cfg.P.d - 1)).2.2 = 0 := by
    obtain ⟨_, _, _, _, hIloop, _, _, _, _, _, _, _, _, _, _, _, _, hData, _⟩ := H.loop
    have hD := (hData (cfg.P.d - 1) (Nat.zero_le _) (by omega)).2
    have hUS := (hIloop.slotModel (cfg.P.d - 1) (by omega)).2.2.2.2.2.2.2.2.1
    have hCur := hIloop.curULink
    have hUS' : H.levelUS (cfg.P.d - 1) = [] := by
      have h1 : cfg.P.d - 1 + 1 = H.i₀ := by omega
      rw [h1, hCur, hEmpty] at hUS
      exact hUS.symm
    rw [← hD, hUS']
    rfl
  obtain ⟨_, _, hℓ0Eq, _, _, _, _, _, ⟨_, vcOf, ecOf, _, _, hModelLoop⟩, _⟩ := H.start.modelInv
  have hG1Eq : H.G1 = (model.chain.G 0).applyBatch H.Uint := H.G1_eq
  have hUintEq : H.Uint =
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2 := H.Uint_eq
  have hModel0 : UpdateLoopModelInv w L P wordExp stretchPrec vcOf ecOf
      (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j) H.ℓ' H.g' cfg.P.d 0 H.st0 H.G1
      H.Uint ((model.chain.G 0).batchEnc H.Uint) (H.st0.levelOrd 0) := by
    rw [H.st0_eq, hG1Eq, hUintEq, H.ℓ'_eq, H.g'_eq, H.gVec_eq, H.lVec_eq]
    exact hModelLoop
  -- Level-0 length stability on surviving edges of `G0`
  have hLenStab0 : ∀ e ∈ H.G1.E, e ∈ (model.chain.G 0).E → (∀ u ∈ H.Uint, ¬ u.Inserts e) →
      ({ H.st0.toTreeChain with G := fun j => if j = 0 then H.G1 else H.st0.G j } :
        TreeChain).chainLen H.ℓ' 0 e = model.chain.toTreeChain.chainLen model.chain.ℓ 0 e := by
    intro e he1 he0 _
    change H.ℓ' e = model.chain.ℓ e
    have hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt
        model.nextFresh := H.start.rep0.2.2.2.2.1
    have hDich := refreshBatch_edge_dichotomy hFresh H.start.refresh
    set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    have heExt : model.intToExt e ∈ model.extG.E := (hFresh.hRight e he0).2
    have he2i : model.extToInt (model.intToExt e) = e := (hFresh.hRight e he0).1
    have hNoInsExt : ¬ ∃ u ∈ U, u.Inserts (model.intToExt e) := by
      intro hIns
      have hDel := (hDich.2.2.2.2 (model.intToExt e) heExt hIns).2.1
      rw [he2i] at hDel
      have hNotMem := notMem_applyBatch_of_delete tr.2.2.2.2 (model.chain.G 0) hDel
        (fun u hu hI => by
          have hP := translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt
            model.intToExt model.nextFresh hFresh H.start.refresh.1
          have hGe := (hP.2.2.2.2.2.2.1 u hu e hI).1
          exact absurd (hFresh.hLtFresh e he0) (by omega))
      rw [H.G1_eq, H.Uint_eq] at he1
      exact hNotMem he1
    have hSurv := hDich.2.2.2.1 (model.intToExt e) heExt hNoInsExt
    rw [H.ℓ'_eq, H.lVec_eq]
    dsimp only
    have hi2e : tr.2.2.1 e = model.intToExt e := by simpa [he2i] using hSurv.2.2.1
    rw [hi2e]
    simp only [updateOverlay, heExt, hNoInsExt, not_false_eq_true, and_self, ↓reduceIte]
    exact (hℓ0Eq e he0).symm
  rw [← hUL]
  exact updateLoop_noFire_last_G hInv cfg.P.d 0 H.st0 H.G1 H.Uint
    ((model.chain.G 0).batchEnc H.Uint) (H.st0.levelOrd 0) hdPos (by omega)
    (by rw [H.st0_eq]; exact hInv.hN0) (by rw [H.st0_eq]; exact hInv.hLvlM)
    (by rw [H.st0_eq]) (by rw [H.st0_eq])
    (fun j _ => by rw [H.st0_eq]; exact ⟨rfl, rfl, rfl⟩)
    (by rw [H.st0_eq]; rfl) (by rw [hUL]; exact hRebEq) hModel0 hLenStab0 hStepLen

end RunFields

end MinCostFlow.MinRatio
