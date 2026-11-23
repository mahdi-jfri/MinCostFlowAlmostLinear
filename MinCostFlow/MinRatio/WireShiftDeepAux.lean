module

public import MinCostFlow.MinRatio.WireShiftDeepPhase4a
import WordRAM.Tactic

/-!
# Deep shift Phases 0–4a postcondition assembly (`WireShiftDeepAux`)

Assembles `shiftDeep_phases_0_to_4a_raw` (`WireShiftDeepPhase4a.lean`, under the layout contract)
into `shiftDeep_phases_0_to_4a_runs`: preserves `oldPtrs` forests across Phases 2–4a, combines
`[0, i0)` and `[i0, d)` core representations, footprints, and disjointness, preserves terminal
level `d` and all `levelMeta` graphs/lengths on `[0, d)`, and telescopes `Rcore.phi` over `Fin d`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program Bundle

set_option maxHeartbeats 800000 in
/-- Execute Phases 0–4a of `shiftDeepChainBodyKFBL` on a non-terminal shift `i < d`. -/
theorem shiftDeep_phases_0_to_4a_runs
    {w L P m V psi k epsExp drainUnit capExp wordExp stretchPrec lastMul
      intCapMax forestEdgeCap deepSpace deepFixed toolMul vCap eCap capLimit fcap restartSpace
      lastSpace initCore coreLenProc edgeProc signExt mul intDiv copy lastInit root heap pos : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {allocation : ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opCore opLast : ℕ → ℕ}
    {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {i : Fin (cfg.P.d + 1)}
    (levelSpace : ℕ → ℕ) (levelCost : Alg2State cfg → Fin (cfg.P.d + 1) → ℕ → ℕ)
    (hCoreLocal : Rcore.Local)
    (hFmtBits : fmt.limbBits = 4) (hFmtPrec : fmt.precision = P) (hWidth : P ≤ 4 * L)
    (hL4W : 4 * L + 2 < 2 ^ w) (hw17 : 17 < 2 ^ w)
    (hkPos : 0 < cfg.P.k) (hkW : cfg.P.k < 2 ^ w) (hdW : cfg.P.d < 2 ^ w) (hN0W : cfg.N₀ < 2 ^ w)
    (hDepthW : Expander.chosenL (cfg.P.M₀ ^ 2) < 2 ^ w)
    (hInitOrdEq : ToolInitOrdEqOnE cfg.T)
    (hCore : DeepShiftCoreKFBL fmt L m vCap eCap capExp cfg Psc allocation Rcore p initCore opCore)
    (hForestCap : DeepShiftForestCapKFBL fmt L vCap eCap capExp cfg Psc allocation fcap Rcore p
      opCore)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hLastImpl : ∀ G : MGraph, G.m ≤ m → G.m ≤ levelM cfg.TP cfg.P cfg.P.d → G.n ≤ G.m + 1 →
      (∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) →
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision G.E).Implements
        w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L G vCap eCap lastMul stretchPrec lastAlloc))
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hOps : DeepShiftOpsHypKFBL (w := w) (L := L) (capExp := capExp) (capLimit := capLimit)
      (fcap := fcap) (lastMul := lastMul) (intCapMax := intCapMax)
      (forestEdgeCap := forestEdgeCap) (deepSpace := deepSpace) (deepFixed := deepFixed)
      (toolMul := toolMul) (fmt := fmt) (cfg := cfg) (Psc := Psc) (allocation := allocation)
      (lastAlloc := lastAlloc) restartSpace levelSpace levelCost lastSpace)
    (hiLt : i.val < cfg.P.d)
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hMemEq : ∀ a, tok.tag a ≠ 5 → mem a = mem0 a)
    (hBranLt : ∀ j < cfg.P.d, model.chain.bran j < cfg.P.k)
    (hModelInv : ShiftDeepModelInv w L P wordExp stretchPrec model i)
    (hModelK : ShiftDeepModelInvKFBL model i)
    (hWordExpEq : Psc.wordExp = wordExp)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < heap)
    (hzHeap : ZeroFrom mem heap)
    (hHeapRoom : heap + deepSpace < 2 ^ w) :
    let d := cfg.P.d
    let model' := alg2LoopShiftStep cfg model i
    let handleBase := tok.handle + 18
    let branchBase := handleBase + (d + 1)
    let levelMeta := solverLevelMetaAddr tok.table d
    let phase04a : Stmt :=
      shiftDeepInitRegsKFBL ;;
      shiftDeepCollectOldKFBL (opCore 2) ;;
      shiftDeepRestartAndReadoutKFBL (opCore 1) (opCore 3) (opCore 2) coreLenProc (opCore 5) ;;
      ordRebuildSuffixProgramKFBLStore initCore (opCore 3) (opCore 2) coreLenProc (opCore 5)
        lastInit ;;
      (.assign 20 (.reg 71) ;; collectLSFForestsLoop (opCore 2) 81 ;; collectTermForestStmt 81)
    ∃ (s5 : State) (c04a newTermH newTermTok : ℕ)
      (newCoreHandle : ℕ → ℕ) (newCoreTok : ℕ → Rcore.τ),
      Runs w p ω phase04a (startState [root, i.val, heap] mem pos) .normal s5 c04a ∧
      heap + 2 * (d - i.val + 1) ≤ s5.regs 4 ∧
      s5.regs 4 + 3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L) ≤ heap + deepSpace ∧
      ZeroFrom s5.mem (s5.regs 4) ∧
      s5.regs 70 = root ∧ s5.regs 71 = i.val ∧ s5.regs 73 = tok.handle ∧
      s5.regs 75 = d ∧ s5.regs 79 = d - i.val + 1 ∧
      s5.regs 80 = heap ∧ s5.regs 81 = heap + (d - i.val + 1) ∧
      ForestPtrListAt s5.mem heap (chainSuffixForests model.chain i.val) tok.intCap (s5.regs 4) ∧
      ForestPtrListAt s5.mem (heap + (d - i.val + 1)) (chainSuffixForests model'.chain i.val)
        tok.intCap (s5.regs 4) ∧
      (∀ j < d,
        (j ≤ i.val → newCoreHandle j = tok.coreHandle j) ∧
        (j < i.val → newCoreTok j = tok.coreTok j) ∧
        (i.val < j → heap ≤ newCoreHandle j ∧ newCoreHandle j ≤ s5.regs 4) ∧
        s5.mem (handleBase + j) = newCoreHandle j ∧
        s5.mem (branchBase + j) = model'.chain.bran j ∧
        Rcore.rep (newCoreHandle j) (chainLevelOrdAbs model'.chain j) (newCoreTok j) s5.mem ∧
        (∀ a, Rcore.foot (newCoreHandle j) (newCoreTok j) a →
          (j ≤ i.val ∧ Rcore.foot (tok.coreHandle j) (tok.coreTok j) a) ∨
          (heap ≤ a ∧ a < s5.regs 4))) ∧
      (∀ j₁ < d, ∀ j₂ < d, j₁ ≠ j₂ →
        ∀ a, Rcore.foot (newCoreHandle j₁) (newCoreTok j₁) a →
          ¬ Rcore.foot (newCoreHandle j₂) (newCoreTok j₂) a) ∧
      s5.mem (handleBase + d) = newTermH ∧
      s5.mem (branchBase + d) = model'.chain.lastBran ∧
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (model'.chain.G d).E).rep
        newTermH (model'.chain.lastK, model'.chain.lastLSFs) newTermTok s5.mem ∧
      (∀ a, (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (model'.chain.G d).E).foot
          newTermH newTermTok a →
        heap ≤ a ∧ a < s5.regs 4 ∧ ∀ j < d, ¬ Rcore.foot (newCoreHandle j) (newCoreTok j) a) ∧
      (∀ j < d,
        DynGraphAt s5.mem (s5.mem (levelMeta + d + j)) vCap eCap (model'.chain.G j) ∧
        EdgeValuesAt s5.mem (s5.mem (levelMeta + j)) 4 L P (model'.chain.G j).E
          (model'.chain.toTreeChain.chainLen model'.chain.ℓ j) ∧
        (j ≤ i.val → s5.mem (levelMeta + j) = mem0 (levelMeta + j) ∧
          s5.mem (levelMeta + d + j) = mem0 (levelMeta + d + j)) ∧
        (i.val < j →
          heap ≤ s5.mem (levelMeta + j) ∧ s5.mem (levelMeta + j) + eCap * L ≤ s5.regs 4 ∧
          heap ≤ s5.mem (levelMeta + d + j) ∧
          s5.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ s5.regs 4 ∧
          (∀ a, s5.mem (levelMeta + j) ≤ a → a < s5.mem (levelMeta + j) + eCap * L →
            ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P
                (model'.chain.G d).E).foot newTermH newTermTok a ∧
            ∀ r < d, ¬ Rcore.foot (newCoreHandle r) (newCoreTok r) a) ∧
          (∀ a, s5.mem (levelMeta + d + j) ≤ a →
            a < s5.mem (levelMeta + d + j) + dynGraphSize vCap eCap →
            ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P
                (model'.chain.G d).E).foot newTermH newTermTok a ∧
            ∀ r < d, ¬ Rcore.foot (newCoreHandle r) (newCoreTok r) a))) ∧
      ((∀ j, i.val < j → j < d →
          s5.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ s5.mem (levelMeta + j)) ∧
       (∀ j₁ j₂, i.val < j₁ → j₁ < j₂ → j₂ < d →
          s5.mem (levelMeta + j₁) + eCap * L ≤ s5.mem (levelMeta + d + j₂))) ∧
      (∀ a < heap, tok.tag a ≠ 4 → tok.tag a ≠ 22 + d →
        (∀ j, i.val ≤ j → j < d → tok.tag a ≠ 21 + j) → s5.mem a = mem a) ∧
      c04a + (∑ j : Fin d, Rcore.phi (newCoreHandle j.val) (newCoreTok j.val) s5.mem) +
        85 * (graphListEdgeSum (chainSuffixForests model.chain i.val) +
          graphListEdgeSum (chainSuffixForests model'.chain i.val)) + 210 * (d + 1) + 400 ≤
        deepFixed + toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
          (∑ j : Fin d, Rcore.phi (tok.coreHandle j.val) (tok.coreTok j.val) mem0) := by
  dsimp only
  let d := cfg.P.d
  let i0 := i.val
  let chain := model.chain
  let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P chain i0).1
  have hChain' : (alg2LoopShiftStep cfg model i).chain = next := by
    simp [alg2LoopShiftStep, next, chain, i0]
  let handleBase := tok.handle + 18
  let branchBase := handleBase + (d + 1)
  let lvlMTable := solverLvlMAddr tok.table cfg.P.d
  let levelMeta := solverLevelMetaAddr tok.table cfg.P.d
  let cnt := d - i0 + 1
  let heap1 := heap + 2 * cnt
  obtain ⟨s2, s3, s4, s5, c04a, newTermTok, yI0_2, yI0_3,
      coreTok4, coreTok5, rAll, hs2_lo, h4Lo3, hs4_lo, hs5_lo, hS5Space, hz5, hOldForestsSafe2,
      hFootI0_2, hs2_frame, _, hFootI0_3, hH3, hLen3, h6Lo3, hHEnd3, h6Disj3, h7Lo3, hLenEnd3,
      h7Disj3, h6Le7_3, hMeta3, hs3_frame, hCores4, hMeta4, hMetaOrd4, hTermB4, hTermRep4, hTermFoot4, hTermDisj4,
      hs4_frame, hNewForests5, hCores5_ico, hCoreDisj5_ico, hs5_frame,
      h5_70, h5_71, h5_73, h5_75, h5_79, h5_80, h5_81, hc04a⟩ :=
    shiftDeep_phases_0_to_4a_raw (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi)
      (k := k) (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (wordExp := wordExp)
      (stretchPrec := stretchPrec) (lastMul := lastMul) (intCapMax := intCapMax)
      (forestEdgeCap := forestEdgeCap) (deepSpace := deepSpace) (deepFixed := deepFixed)
      (toolMul := toolMul) (vCap := vCap) (eCap := eCap) (capLimit := capLimit) (fcap := fcap)
      (restartSpace := restartSpace)
      (lastSpace := lastSpace) (initCore := initCore) (coreLenProc := coreLenProc)
      (edgeProc := edgeProc) (signExt := signExt) (mul := mul) (intDiv := intDiv) (copy := copy)
      (lastInit := lastInit) (root := root) (heap := heap) (pos := pos) (fmt := fmt) (cfg := cfg)
      (Psc := Psc) (allocation := allocation) (lastAlloc := lastAlloc) (Rcore := Rcore) (p := p)
      (opCore := opCore) (opLast := opLast) (ω := ω) (mem0 := mem0) (mem := mem) (model := model)
      (tok := tok) (i := i) levelSpace levelCost hCoreLocal hFmtBits hFmtPrec hWidth hL4W hw17
      hkPos hkW hdW hN0W hDepthW hInitOrdEq hCore hForestCap hcapLim hLastImpl hCoreLenProc
      hEdgeProc hSign hMul hDiv hCopy hOps hiLt hRep0 hMeta0 hCaps0 hMemEq hBranLt hModelInv
      hModelK hWordExpEq hFootLt hzHeap hHeapRoom
  -- Unpack minimal tags/metadata and clear heavy hypotheses
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hCores0, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, _, _, _, hT4, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT21⟩ := hTags0
  have hMetaCaps := SolverLevelMetaAt.atCaps hMeta0 hCaps0
  obtain ⟨_, _, _, _, hTagMeta0, _⟩ := hMeta0
  clear hModelInv hModelK hOps hCore hForestCap hLastImpl hCoreLenProc hEdgeProc hSign hMul hDiv
    hCopy hInitOrdEq
  obtain ⟨hExG, hExPre, _, _, _, _, _, _, _, _, _, _, _, hExEll, _, _, _⟩ :=
    ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P chain hiLt
  have hdPos : 0 < d := Nat.zero_lt_of_lt hiLt
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < heap := hFootLt a (Or.inl (hOwnOfTag a h))
  have hmem0_eq {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 5) : mem a = mem0 a := hMemEq a (ht ▸ hv)
  have hTagHandle (j : ℕ) (hj : j ≤ d) : tok.tag (handleBase + j) = 4 := hT4 j (by omega)
  have hTagBranch (j : ℕ) (hj : j ≤ d) : tok.tag (branchBase + j) = 4 := by
    have := hT4 ((d + 1) + j) (by omega)
    rwa [show tok.handle + 18 + ((d + 1) + j) = branchBase + j by dsimp [branchBase, handleBase]; omega] at this
  have hTagMetaG (j : ℕ) (hj : j < d) : tok.tag (levelMeta + d + j) = 22 + d := by
    have := hTagMeta0 (d + j) (by omega)
    rwa [show levelMeta + (d + j) = levelMeta + d + j by omega] at this
  have hTagMetaL (j : ℕ) (hj : j < d) : tok.tag (levelMeta + j) = 22 + d := hTagMeta0 j (by omega)
  have hLevelEnd : branchBase + d < heap := htagLt (by rw [hTagBranch d le_rfl]; decide)
  have hH_end : handleBase + d < heap :=
    lt_trans (Nat.lt_of_lt_of_le (by dsimp [branchBase, handleBase]; omega) (Nat.le_add_right branchBase d)) hLevelEnd
  have hMetaEnd : levelMeta + 2 * d ≤ heap := by
    have h1 := hTagMeta0 (2 * d - 1) (Nat.sub_lt (Nat.mul_pos (by decide) hdPos) Nat.one_pos)
    have h3 := htagLt (by rw [h1]; omega)
    dsimp only [levelMeta, lvlMTable, d] at h3 ⊢; omega
  have hCoreFootLt (j : ℕ) (hj : j < d) (a : ℕ) (ha : Rcore.foot (tok.coreHandle j) (tok.coreTok j) a) :
      a < heap := htagLt (by rw [hT21 j hj a ha]; omega)
  have hCoreDisj0 (j₁ j₂ : ℕ) (h1 : j₁ < d) (h2 : j₂ < d) (hne : j₁ ≠ j₂) (a : ℕ)
      (ha1 : Rcore.foot (tok.coreHandle j₁) (tok.coreTok j₁) a)
      (ha2 : Rcore.foot (tok.coreHandle j₂) (tok.coreTok j₂) a) : False := by
    have := (hT21 j₁ h1 a ha1).symm.trans (hT21 j₂ h2 a ha2); omega
  have hs3_geHeap1 : heap1 ≤ s3.regs 4 := hs2_lo.trans h4Lo3
  have hHeapLeS2 : heap ≤ s2.regs 4 := le_trans (Nat.le_add_right heap _) hs2_lo
  have hHeapLeS3 : heap ≤ s3.regs 4 := le_trans hHeapLeS2 h4Lo3
  have hHeapLeS4 : heap ≤ s4.regs 4 := le_trans hHeapLeS3 hs4_lo
  have hHeapLeS5 : heap ≤ s5.regs 4 := le_trans hHeapLeS4 hs5_lo
  have hSepHB : handleBase + d < branchBase ∨ branchBase + d < handleBase :=
    Or.inl (by dsimp [branchBase, handleBase]; omega)
  have hSepHL : handleBase + d < levelMeta ∨ levelMeta + 2 * d ≤ handleBase :=
    (interval_disj_of_tags (Nat.succ_pos d) (Nat.mul_pos (by decide) hdPos)
      (fun j hj => hTagHandle j (Nat.lt_succ_iff.mp hj)) hTagMeta0 (by omega)).imp
      (fun h => Nat.lt_of_succ_le h) id
  have hSepBL : branchBase + d < levelMeta ∨ levelMeta + 2 * d ≤ branchBase :=
    (interval_disj_of_tags (Nat.succ_pos d) (Nat.mul_pos (by decide) hdPos)
      (fun j hj => hTagBranch j (Nat.lt_succ_iff.mp hj)) hTagMeta0 (by omega)).imp
      (fun h => Nat.lt_of_succ_le h) id
  let coreHandle4 : ℕ → ℕ := fun j => if j = i0 then tok.coreHandle i0 else s4.mem (handleBase + j)
  let coreTok4' : ℕ → Rcore.τ := fun j => if j = i0 then yI0_3 else coreTok4 j
  set newTermH := s4.mem (handleBase + d)
  have hNotFoot2 {a : ℕ} (ha : a < heap) (hne : tok.tag a ≠ 21 + i0) :
      ¬ Rcore.foot (tok.coreHandle i0) yI0_2 a := fun hf => by
    rcases hFootI0_2 a hf with h0 | ⟨hlo, _⟩
    · exact hne (hT21 i0 hiLt a h0)
    · exact absurd (lt_of_lt_of_le ha (le_trans (Nat.le_add_right heap _) hlo)) (Nat.lt_irrefl _)
  have hCellDisj4 (r : ℕ) (hr1 : i0 ≤ r) (hr2 : r < d) {a : ℕ} (ha : a < heap)
      (hnt : tok.tag a ≠ 21 + i0) : ¬ Rcore.foot (coreHandle4 r) (coreTok4' r) a := by
    by_cases hri : r = i0
    · subst hri; simp only [coreHandle4, coreTok4', ↓reduceIte]
      intro hf; rcases hFootI0_3 a hf with h2 | ⟨hlo, _⟩
      · exact hNotFoot2 ha hnt h2
      · exact absurd (lt_of_lt_of_le ha (le_trans hHeapLeS2 hlo)) (Nat.lt_irrefl _)
    · simp only [coreHandle4, coreTok4', hri, ↓reduceIte]
      intro hf; exact absurd (lt_of_lt_of_le ha (le_trans hHeapLeS3 ((hCores4 r (by omega) hr2).2.2.2.2 a hf).1)) (Nat.lt_irrefl _)
  have hY3FootLt (a : ℕ) (ha : Rcore.foot (tok.coreHandle i0) yI0_3 a) : a < s3.regs 4 := by
    rcases hFootI0_3 a ha with h2 | ⟨_, hhi⟩
    · rcases hFootI0_2 a h2 with h0 | ⟨_, hhi2⟩
      · exact (hCoreFootLt i0 hiLt a h0).trans_le hHeapLeS3
      · exact hhi2.trans_le h4Lo3
    · exact hhi
  have hs2_eq_mem0 {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv5 : v ≠ 5)
      (hvC : ∀ j, i0 ≤ j → j < d → v ≠ 21 + j) : s2.mem a = mem0 a := by
    have hlt := htagLt (ht ▸ hv0)
    rw [hs2_frame a (lt_of_lt_of_le hlt (Nat.le_add_right heap _))
      (fun j hj1 hj2 hf => hvC j hj1 hj2 (ht.symm.trans (hT21 j hj2 a hf))) (Or.inl hlt), hmem0_eq ht hv5]
  -- Frame below `heap` across all 5 phases
  have hFrame5 (a : ℕ) (ha : a < heap) (ht4 : tok.tag a ≠ 4) (ht22 : tok.tag a ≠ 22 + d)
      (htC : ∀ j, i0 ≤ j → j < d → tok.tag a ≠ 21 + j) : s5.mem a = mem a := by
    have hneH := (not_mem_interval_of_tag_ne (b := handleBase) (lo := i0 + 1) (hi := d + 1)
      (fun k _ hk => hTagHandle k (Nat.lt_succ_iff.mp hk)) ht4).imp id Nat.lt_of_succ_le
    have hneB := (not_mem_interval_of_tag_ne (b := branchBase) (lo := i0 + 1) (hi := d + 1)
      (fun k _ hk => hTagBranch k (Nat.lt_succ_iff.mp hk)) ht4).imp id Nat.lt_of_succ_le
    have hneM : (a < levelMeta + (i0 + 1 + 1) ∨ levelMeta + d ≤ a) ∧
        (a < levelMeta + d + (i0 + 1 + 1) ∨ levelMeta + 2 * d ≤ a) :=
      (not_mem_interval_of_tag_ne (b := levelMeta) (lo := 0) (hi := 2 * d)
        (fun k _ hk => hTagMeta0 k hk) ht22).elim
        (fun h => ⟨Or.inl (by omega), Or.inl (by omega)⟩) (fun h => ⟨Or.inr (by omega), Or.inr h⟩)
    rw [hs5_frame a (lt_of_lt_of_le ha hHeapLeS4) (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 ha (htC i0 le_rfl hiLt))
        (Or.inl (lt_of_lt_of_le ha (Nat.le_add_right heap _))),
      hs4_frame a (lt_of_lt_of_le ha hHeapLeS3) hneH hneB hneM,
      hs3_frame a (lt_of_lt_of_le ha hHeapLeS2) (hNotFoot2 ha (htC i0 le_rfl hiLt))
        (fun h => ht4 (h ▸ hTagBranch i0 (le_of_lt hiLt)))
        (fun hlt => ⟨fun h => ht22 (h ▸ hTagMetaL (i0 + 1) hlt), fun h => ht22 (h ▸ hTagMetaG (i0 + 1) hlt)⟩),
      hs2_frame a (lt_of_lt_of_le ha (Nat.le_add_right heap _))
        (fun j hj1 hj2 hf => htC j hj1 hj2 (hT21 j hj2 a hf)) (Or.inl ha)]
  -- Preserve `oldPtrs` forests from `s2` to `s5`
  have hOldForests5 : ForestPtrListAt s5.mem heap (chainSuffixForests chain i0) tok.intCap (s5.regs 4) := by
    refine ⟨by rw [chainSuffixForests_length]; exact le_trans (by dsimp only [heap1]; omega) (le_trans hs3_geHeap1 (le_trans hs4_lo hs5_lo)),
      fun t ht => ?_⟩
    obtain ⟨vcT, ecT, hDGT, hEndT, hCapT, hSafeT⟩ := hOldForestsSafe2 t ht
    have htLen : t < cnt := by rw [chainSuffixForests_length] at ht; exact ht
    have hPtLt1 : heap + t < heap1 := by dsimp only [heap1]; omega
    have hPtr5 : s5.mem (heap + t) = s2.mem (heap + t) := by
      have hnf2 : ¬ Rcore.foot (tok.coreHandle i0) yI0_2 (heap + t) := fun hf => by
        rcases hFootI0_2 _ hf with h0 | ⟨hlo2, _⟩
        · exact absurd (lt_of_lt_of_le (hCoreFootLt i0 hiLt _ h0) (Nat.le_add_right heap t)) (Nat.lt_irrefl _)
        · exact absurd (lt_of_lt_of_le hPtLt1 hlo2) (Nat.lt_irrefl _)
      have hnf4 : ∀ j, i0 ≤ j → j < d → ¬ Rcore.foot (coreHandle4 j) (coreTok4' j) (heap + t) := by
        intro j hj1 hj2 hf
        by_cases hji : j = i0
        · subst hji; simp only [coreHandle4, coreTok4', ↓reduceIte] at hf
          rcases hFootI0_3 _ hf with h2 | ⟨hlo, _⟩
          · exact hnf2 h2
          · exact absurd (lt_of_lt_of_le hPtLt1 (le_trans hs2_lo hlo)) (Nat.lt_irrefl _)
        · simp only [coreHandle4, coreTok4', hji, ↓reduceIte] at hf
          exact absurd (lt_of_lt_of_le hPtLt1 (le_trans hs3_geHeap1 ((hCores4 j (by omega) hj2).2.2.2.2 _ hf).1)) (Nat.lt_irrefl _)
      rw [hs5_frame _ (lt_of_lt_of_le hPtLt1 (le_trans hs3_geHeap1 hs4_lo)) hnf4 (Or.inl (Nat.add_lt_add_left htLen heap)),
        hs4_frame _ (lt_of_lt_of_le hPtLt1 hs3_geHeap1)
          (Or.inr (lt_of_lt_of_le hH_end (Nat.le_add_right heap t)))
          (Or.inr (lt_of_lt_of_le hLevelEnd (Nat.le_add_right heap t)))
          ⟨Or.inr (le_trans (by omega) (le_trans hMetaEnd (Nat.le_add_right heap t))),
           Or.inr (le_trans hMetaEnd (Nat.le_add_right heap t))⟩,
        hs3_frame _ (lt_of_lt_of_le hPtLt1 hs2_lo) hnf2
          (Nat.ne_of_gt (lt_of_lt_of_le (lt_trans (Nat.add_lt_add_left hiLt branchBase) hLevelEnd) (Nat.le_add_right heap t)))
          (fun hlt => ⟨Nat.ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (by omega : levelMeta + (i0 + 1) < levelMeta + 2 * d) hMetaEnd) (Nat.le_add_right heap t)),
            Nat.ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (by omega : levelMeta + d + (i0 + 1) < levelMeta + 2 * d) hMetaEnd) (Nat.le_add_right heap t))⟩)]
    refine ⟨vcT, ecT, ?_, hPtr5.symm ▸ (hEndT.trans (h4Lo3.trans (hs4_lo.trans hs5_lo))), hCapT⟩
    rw [hPtr5]
    exact dynGraphAt_of_agree hDGT (fun a ha1 ha2 => by
      obtain ⟨hnf2, hTagS, hOut1⟩ := hSafeT a ha1 ha2
      have haLt2 : a < s2.regs 4 := lt_of_lt_of_le ha2 hEndT
      have hnf4 : ∀ j, i0 ≤ j → j < d → ¬ Rcore.foot (coreHandle4 j) (coreTok4' j) a := by
        intro j hj1 hj2 hf
        by_cases hji : j = i0
        · subst hji; simp only [coreHandle4, coreTok4', ↓reduceIte] at hf
          rcases hFootI0_3 a hf with h2 | ⟨hlo, _⟩
          · exact hnf2 h2
          · exact absurd (lt_of_lt_of_le haLt2 hlo) (Nat.lt_irrefl _)
        · simp only [coreHandle4, coreTok4', hji, ↓reduceIte] at hf
          exact absurd (lt_of_lt_of_le (lt_of_lt_of_le haLt2 h4Lo3) ((hCores4 j (by omega) hj2).2.2.2.2 a hf).1) (Nat.lt_irrefl _)
      have hneH : a < handleBase + (i0 + 1) ∨ handleBase + d < a :=
        hOut1.elim (fun hlt => (not_mem_interval_of_tag_ne (b := handleBase) (lo := i0 + 1) (hi := d + 1)
          (fun k _ hk => hTagHandle k (Nat.lt_succ_iff.mp hk)) (hTagS hlt).1).imp id Nat.lt_of_succ_le)
          (fun hge => Or.inr (lt_of_lt_of_le hH_end (le_trans (Nat.le_add_right heap _) hge)))
      have hneB : a < branchBase + (i0 + 1) ∨ branchBase + d < a :=
        hOut1.elim (fun hlt => (not_mem_interval_of_tag_ne (b := branchBase) (lo := i0 + 1) (hi := d + 1)
          (fun k _ hk => hTagBranch k (Nat.lt_succ_iff.mp hk)) (hTagS hlt).1).imp id Nat.lt_of_succ_le)
          (fun hge => Or.inr (lt_of_lt_of_le hLevelEnd (le_trans (Nat.le_add_right heap _) hge)))
      have hneM : (a < levelMeta + (i0 + 1 + 1) ∨ levelMeta + d ≤ a) ∧
          (a < levelMeta + d + (i0 + 1 + 1) ∨ levelMeta + 2 * d ≤ a) :=
        hOut1.elim (fun hlt => (not_mem_interval_of_tag_ne (b := levelMeta) (lo := 0) (hi := 2 * d)
            (fun k _ hk => hTagMeta0 k hk) (hTagS hlt).2).elim
            (fun h => ⟨Or.inl (by omega), Or.inl (by omega)⟩) (fun h => ⟨Or.inr (by omega), Or.inr h⟩))
          (fun hge => ⟨Or.inr (le_trans (by omega) (le_trans hMetaEnd (le_trans (Nat.le_add_right heap _) hge))),
            Or.inr (le_trans hMetaEnd (le_trans (Nat.le_add_right heap _) hge))⟩)
      rw [hs5_frame a (lt_of_lt_of_le haLt2 (le_trans h4Lo3 hs4_lo)) hnf4
          (hOut1.elim (fun hlt => Or.inl (lt_of_lt_of_le hlt (Nat.le_add_right heap _)))
            (fun hge => Or.inr (le_trans (show heap + cnt + (d - i0 + 1) ≤ heap + 2 * (d - i0 + 1) by dsimp only [cnt]; omega) hge))),
        hs4_frame a (lt_of_lt_of_le haLt2 h4Lo3) hneH hneB hneM,
        hs3_frame a haLt2 hnf2
          (fun h => by have := hTagBranch i0 (le_of_lt hiLt); rw [← h] at this; exact (hTagS (htagLt (by rw [this]; decide))).1 this)
          (fun hlt => ⟨fun h => by have := hTagMetaL (i0 + 1) hlt; rw [← h] at this; exact (hTagS (htagLt (by rw [this]; omega))).2 this,
            fun h => by have := hTagMetaG (i0 + 1) hlt; rw [← h] at this; exact (hTagS (htagLt (by rw [this]; omega))).2 this⟩)])
  -- Combine `[0, i0)` and `[i0, d)` core handles, tokens, and `Rcore.phi`
  let newCoreHandle : ℕ → ℕ := fun j => if j ≤ i0 then tok.coreHandle j else s4.mem (handleBase + j)
  let newCoreTok : ℕ → Rcore.τ := fun j => if j < i0 then tok.coreTok j else coreTok5 j
  have hNewHandleGe (j : ℕ) (hj : i0 ≤ j) : newCoreHandle j = coreHandle4 j := by
    by_cases hji : j = i0
    · subst hji; simp [newCoreHandle, coreHandle4]
    · simp [newCoreHandle, coreHandle4, hji, show ¬ j ≤ i0 by omega]
  have hPreCore5 (j : ℕ) (hj : j < i0) :
      s5.mem (handleBase + j) = tok.coreHandle j ∧
      s5.mem (branchBase + j) = next.bran j ∧
      Rcore.rep (tok.coreHandle j) (chainLevelOrdAbs next j) (tok.coreTok j) s5.mem ∧
      Rcore.phi (tok.coreHandle j) (tok.coreTok j) s5.mem =
        Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0 := by
    have hAbsJ := (ordAlgorithm1_shift_levelOrdAbs_le cfg.T cfg.L cfg.P chain hiLt).1 j hj
    have hloc := hCoreLocal (tok.coreHandle j) (chainLevelOrdAbs chain j) (tok.coreTok j) mem0 s5.mem
      (fun a ha => by
        have ht := hT21 j (by omega) a ha
        exact ((hFrame5 a (hCoreFootLt j (by omega) a ha) (by rw [ht]; omega) (by rw [ht]; omega)
          (fun r hr1 _ => by rw [ht]; omega)).trans (hmem0_eq ht (by omega))).symm)
    have hHjLt : handleBase + j < heap := lt_trans (Nat.add_lt_add_left (by omega) handleBase) hH_end
    have hBjLt : branchBase + j < heap := lt_trans (Nat.add_lt_add_left (by omega) branchBase) hLevelEnd
    have hH5j : s5.mem (handleBase + j) = tok.coreHandle j := by
      rw [hs5_frame _ (lt_of_lt_of_le hHjLt hHeapLeS4)
          (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 hHjLt (by rw [hTagHandle j (by omega)]; omega))
          (Or.inl (lt_of_lt_of_le hHjLt (Nat.le_add_right heap _))),
        hs4_frame _ (lt_of_lt_of_le hHjLt hHeapLeS3) (Or.inl (by omega))
          (by rcases hSepHB with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
          (by rcases hSepHL with h | h <;> [exact ⟨Or.inl (by omega), Or.inl (by omega)⟩; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩]),
        hs3_frame _ (lt_of_lt_of_le hHjLt hHeapLeS2)
          (hNotFoot2 hHjLt (by rw [hTagHandle j (by omega)]; omega)) (by dsimp [branchBase]; omega)
          (fun hlt => ⟨fun h => by have := hTagHandle j (by omega); rw [h, hTagMetaL (i0 + 1) hlt] at this; omega,
            fun h => by have := hTagHandle j (by omega); rw [h, hTagMetaG (i0 + 1) hlt] at this; omega⟩)]
      exact (hs2_eq_mem0 (hTagHandle j (by omega)) (by decide) (by decide) (fun _ _ _ => by omega)).trans (hCores0 j (by omega)).1
    have hB5j : s5.mem (branchBase + j) = next.bran j := by
      rw [hs5_frame _ (lt_of_lt_of_le hBjLt hHeapLeS4)
          (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 hBjLt (by rw [hTagBranch j (by omega)]; omega))
          (Or.inl (lt_of_lt_of_le hBjLt (Nat.le_add_right heap _))),
        hs4_frame _ (lt_of_lt_of_le hBjLt hHeapLeS3)
          (by rcases hSepHB with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)]) (Or.inl (by omega))
          (by rcases hSepBL with h | h <;> [exact ⟨Or.inl (by omega), Or.inl (by omega)⟩; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩]),
        hs3_frame _ (lt_of_lt_of_le hBjLt hHeapLeS2)
          (hNotFoot2 hBjLt (by rw [hTagBranch j (by omega)]; omega)) (by omega)
          (fun hlt => ⟨fun h => by have := hTagBranch j (by omega); rw [h, hTagMetaL (i0 + 1) hlt] at this; omega,
            fun h => by have := hTagBranch j (by omega); rw [h, hTagMetaG (i0 + 1) hlt] at this; omega⟩),
        hs2_eq_mem0 (hTagBranch j (by omega)) (by decide) (by decide) (fun _ _ _ => by omega),
        (hCores0 j (by omega)).2.1, (hExPre j hj).2.1]
    exact ⟨hH5j, hB5j, hAbsJ.symm ▸ hloc.1 (hCores0 j (by omega)).2.2, hloc.2.symm⟩
  -- Preserve terminal level `d` from `s4` to `s5`
  have hTermPres5 :
      s5.mem (handleBase + d) = newTermH ∧ s5.mem (branchBase + d) = next.lastBran ∧
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (next.G d).E).rep
        newTermH (next.lastK, next.lastLSFs) newTermTok s5.mem := by
    refine ⟨hs5_frame _ (lt_of_lt_of_le hH_end hHeapLeS4)
        (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 hH_end (by rw [hTagHandle d le_rfl]; omega))
        (Or.inl (lt_of_lt_of_le hH_end (Nat.le_add_right heap _))),
      (hs5_frame _ (lt_of_lt_of_le hLevelEnd hHeapLeS4)
        (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 hLevelEnd (by rw [hTagBranch d le_rfl]; omega))
        (Or.inl (lt_of_lt_of_le hLevelEnd (Nat.le_add_right heap _)))).trans hTermB4,
      (LastLevelProgram.lastLevelRepresentation_local vCap eCap 4 L P (next.G d).E
        newTermH (next.lastK, next.lastLSFs) newTermTok s4.mem s5.mem (fun a ha => by
          have hGe3 := (hTermFoot4 a ha).1
          have hLt4 := (hTermFoot4 a ha).2
          refine (hs5_frame a hLt4 (fun r hr1 hr2 hf => ?_)
            (Or.inr (le_trans (by dsimp only [heap1]; omega) (le_trans hs3_geHeap1 hGe3)))).symm
          by_cases hri : r = i0
          · subst hri; dsimp only [i0] at hf; simp only [↓reduceIte] at hf
            exact absurd (lt_of_lt_of_le (hY3FootLt a hf) hGe3) (Nat.lt_irrefl _)
          · dsimp only [i0] at hri hf; simp only [hri, ↓reduceIte] at hf
            exact hTermDisj4 r (by omega) hr2 a ha hf)).1
        (hFmtPrec ▸ hTermRep4)⟩
  rw [hChain']
  refine ⟨s5, c04a, newTermH, newTermTok, newCoreHandle, newCoreTok,
    rAll, le_trans hs3_geHeap1 (le_trans hs4_lo hs5_lo), hS5Space, hz5,
    h5_70, h5_71, h5_73, h5_75, h5_79, h5_80, h5_81,
    hOldForests5, hNewForests5, ?_, ?_, hTermPres5.1, hTermPres5.2.1, hTermPres5.2.2, ?_, ?_, ?_,
    hFrame5, ?_⟩
  · -- `hCores5`
    intro j hj
    by_cases hlt : j < i0
    · obtain ⟨hH, hB, hRep, _⟩ := hPreCore5 j hlt
      simp only [newCoreHandle, newCoreTok, show j ≤ i0 by omega, hlt, ↓reduceIte]
      exact ⟨fun _ => trivial, fun _ => trivial, fun h => by omega, hH, hB, hRep, fun a ha => Or.inl ⟨by omega, ha⟩⟩
    · have hj1 : i0 ≤ j := by omega
      have hH_eq := hNewHandleGe j hj1
      have hTok_eq : newCoreTok j = coreTok5 j := by simp [newCoreTok, hlt]
      obtain ⟨hH4, hB4, hRep5, hFoot5⟩ := hCores5_ico j hj1 hj
      have hHjLt : handleBase + j < heap := lt_trans (Nat.add_lt_add_left hj handleBase) hH_end
      have hBjLt : branchBase + j < heap := lt_trans (Nat.add_lt_add_left hj branchBase) hLevelEnd
      have hH5 : s5.mem (handleBase + j) = newCoreHandle j := by
        rw [hH_eq]
        change s5.mem (handleBase + j) = (if j = i.val then tok.coreHandle i.val else s4.mem (tok.handle + 18 + j))
        dsimp only at hH4; rw [← hH4]
        exact hs5_frame _ (lt_of_lt_of_le hHjLt hHeapLeS4)
          (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 hHjLt (by rw [hTagHandle j (le_of_lt hj)]; omega))
          (Or.inl (lt_of_lt_of_le hHjLt (Nat.le_add_right heap _)))
      have hB5 : s5.mem (branchBase + j) = next.bran j := by
        rw [← hB4]
        exact hs5_frame _ (lt_of_lt_of_le hBjLt hHeapLeS4)
          (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 hBjLt (by rw [hTagBranch j (le_of_lt hj)]; omega))
          (Or.inl (lt_of_lt_of_le hBjLt (Nat.le_add_right heap _)))
      refine ⟨fun hle => by simp [newCoreHandle, show j ≤ i0 from hle], fun h => by omega,
        fun hgt => by
          simp only [newCoreHandle, show ¬ j ≤ i0 by omega, ↓reduceIte]
          have hLo4 := (hCores4 j (by omega) hj).2.1
          have hHi4 := (hCores4 j (by omega) hj).2.2.1
          exact ⟨le_trans hHeapLeS3 hLo4, le_trans hHi4 hs5_lo⟩,
        hH5, hB5, hH_eq.symm ▸ hTok_eq.symm ▸ hRep5, fun a ha => ?_⟩
      rw [hH_eq, hTok_eq] at ha
      rcases hFoot5 a ha with h4 | ⟨hlo, hhi⟩
      · by_cases hji : j = i0
        · subst hji; dsimp only [i0] at h4; simp only [↓reduceIte] at h4
          rcases hFootI0_3 a h4 with h2 | ⟨hlo3, hhi3⟩
          · rcases hFootI0_2 a h2 with h0 | ⟨hlo2, hhi2⟩
            · exact Or.inl ⟨le_rfl, h0⟩
            · exact Or.inr ⟨le_trans (Nat.le_add_right heap _) hlo2, lt_of_lt_of_le hhi2 (le_trans h4Lo3 (le_trans hs4_lo hs5_lo))⟩
          · exact Or.inr ⟨le_trans hHeapLeS2 hlo3, lt_of_lt_of_le hhi3 (le_trans hs4_lo hs5_lo)⟩
        · dsimp only [i0] at hji h4; simp only [hji, ↓reduceIte] at h4
          have h4b := (hCores4 j (by omega) hj).2.2.2.2 a h4
          exact Or.inr ⟨le_trans hHeapLeS3 h4b.1, lt_of_lt_of_le h4b.2 hs5_lo⟩
      · exact Or.inr ⟨le_trans hHeapLeS4 hlo, hhi⟩
  · -- `hCoreDisj5`
    intro j₁ h1 j₂ h2 hne a ha1 ha2
    by_cases l1 : j₁ < i0 <;> by_cases l2 : j₂ < i0
    · simp only [newCoreHandle, newCoreTok, show j₁ ≤ i0 by omega, show j₂ ≤ i0 by omega, l1, l2, ↓reduceIte] at ha1 ha2
      exact hCoreDisj0 j₁ j₂ h1 h2 hne a ha1 ha2
    · rw [hNewHandleGe j₂ (by omega)] at ha2
      simp only [newCoreHandle, newCoreTok, show j₁ ≤ i0 by omega, l1, l2, ↓reduceIte] at ha1 ha2
      have hlt1 := hCoreFootLt j₁ h1 a ha1
      rcases (hCores5_ico j₂ (by omega) h2).2.2.2 a ha2 with h4 | ⟨hlo, _⟩
      · by_cases hji : j₂ = i0
        · subst hji; dsimp only [i0] at h4; simp only [↓reduceIte] at h4
          rcases hFootI0_3 a h4 with h2' | ⟨hlo, _⟩
          · rcases hFootI0_2 a h2' with h0 | ⟨hlo2, _⟩
            · exact hCoreDisj0 j₁ i0 h1 hiLt hne a ha1 h0
            · exact absurd (lt_of_lt_of_le hlt1 (le_trans (Nat.le_add_right heap _) hlo2)) (Nat.lt_irrefl _)
          · exact absurd (lt_of_lt_of_le hlt1 (le_trans hHeapLeS2 hlo)) (Nat.lt_irrefl _)
        · dsimp only [i0] at hji h4; simp only [hji, ↓reduceIte] at h4
          exact absurd (lt_of_lt_of_le hlt1 (le_trans hHeapLeS3 ((hCores4 j₂ (by omega) h2).2.2.2.2 a h4).1)) (Nat.lt_irrefl _)
      · exact absurd (lt_of_lt_of_le hlt1 (le_trans hHeapLeS4 hlo)) (Nat.lt_irrefl _)
    · rw [hNewHandleGe j₁ (by omega)] at ha1
      simp only [newCoreHandle, newCoreTok, show j₂ ≤ i0 by omega, l1, l2, ↓reduceIte] at ha1 ha2
      have hlt2 := hCoreFootLt j₂ h2 a ha2
      rcases (hCores5_ico j₁ (by omega) h1).2.2.2 a ha1 with h4 | ⟨hlo, _⟩
      · by_cases hji : j₁ = i0
        · subst hji; dsimp only [i0] at h4; simp only [↓reduceIte] at h4
          rcases hFootI0_3 a h4 with h2' | ⟨hlo, _⟩
          · rcases hFootI0_2 a h2' with h0 | ⟨hlo2, _⟩
            · exact hCoreDisj0 i0 j₂ hiLt h2 hne a h0 ha2
            · exact absurd (lt_of_lt_of_le hlt2 (le_trans (Nat.le_add_right heap _) hlo2)) (Nat.lt_irrefl _)
          · exact absurd (lt_of_lt_of_le hlt2 (le_trans hHeapLeS2 hlo)) (Nat.lt_irrefl _)
        · dsimp only [i0] at hji h4; simp only [hji, ↓reduceIte] at h4
          exact absurd (lt_of_lt_of_le hlt2 (le_trans hHeapLeS3 ((hCores4 j₁ (by omega) h1).2.2.2.2 a h4).1)) (Nat.lt_irrefl _)
      · exact absurd (lt_of_lt_of_le hlt2 (le_trans hHeapLeS4 hlo)) (Nat.lt_irrefl _)
    · rw [hNewHandleGe j₁ (by omega)] at ha1
      rw [hNewHandleGe j₂ (by omega)] at ha2
      simp only [newCoreTok, l1, l2, ↓reduceIte] at ha1 ha2
      exact hCoreDisj5_ico j₁ j₂ (by omega) h1 (by omega) h2 hne a ha1 ha2
  · -- `hTerm5` foot bounds and disjointness
    intro a ha
    have hGe3 := (hTermFoot4 a ha).1
    have hLt4 := (hTermFoot4 a ha).2
    refine ⟨le_trans hHeapLeS3 hGe3, hLt4.trans_le hs5_lo, fun j hj hf => ?_⟩
    by_cases hlt : j < i0
    · simp only [newCoreHandle, newCoreTok, show j ≤ i0 by omega, hlt, ↓reduceIte] at hf
      exact absurd (lt_of_lt_of_le (hCoreFootLt j hj a hf) (le_trans hHeapLeS3 hGe3)) (Nat.lt_irrefl _)
    · rw [hNewHandleGe j (by omega)] at hf; simp only [newCoreTok, hlt, ↓reduceIte] at hf
      rcases (hCores5_ico j (by omega) hj).2.2.2 a hf with h4 | ⟨hlo, _⟩
      · by_cases hji : j = i0
        · subst hji; dsimp only [i0] at h4; simp only [↓reduceIte] at h4
          exact absurd (lt_of_lt_of_le (hY3FootLt a h4) hGe3) (Nat.lt_irrefl _)
        · dsimp only [i0] at hji h4; simp only [hji, ↓reduceIte] at h4
          exact hTermDisj4 j (by omega) hj a ha h4
      · exact absurd (lt_of_lt_of_le hLt4 hlo) (Nat.lt_irrefl _)
  · -- `hMeta5`
    intro j hj
    have hMLt : levelMeta + j < heap := lt_of_lt_of_le (by omega : levelMeta + j < levelMeta + 2 * d) hMetaEnd
    have hGLt : levelMeta + d + j < heap := lt_of_lt_of_le (by omega : levelMeta + d + j < levelMeta + 2 * d) hMetaEnd
    by_cases hle : j ≤ i0
    · obtain ⟨hDGJ, hLenJ, _, hTagLJ, hTagGJ⟩ := hMetaCaps j hj
      have hLPtr5 : s5.mem (levelMeta + j) = mem0 (levelMeta + j) :=
        (hs5_frame _ (lt_of_lt_of_le hMLt hHeapLeS4) (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 hMLt (by rw [hTagMetaL j hj]; omega))
            (Or.inl (lt_of_lt_of_le hMLt (Nat.le_add_right heap _)))).trans
          ((hs4_frame _ (lt_of_lt_of_le hMLt hHeapLeS3)
            (by rcases hSepHL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
            (by rcases hSepBL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
            ⟨Or.inl (by omega), Or.inl (by omega)⟩).trans
            ((hs3_frame _ (lt_of_lt_of_le hMLt hHeapLeS2) (hNotFoot2 hMLt (by rw [hTagMetaL j hj]; omega))
              (fun h => by have := hTagMetaL j hj; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega)
              (fun _ => ⟨by omega, by omega⟩)).trans
              (hs2_eq_mem0 (hTagMetaL j hj) (by omega) (by omega) (fun _ _ _ => by omega))))
      have hGPtr5 : s5.mem (levelMeta + d + j) = mem0 (levelMeta + d + j) :=
        (hs5_frame _ (lt_of_lt_of_le hGLt hHeapLeS4) (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 hGLt (by rw [hTagMetaG j hj]; omega))
            (Or.inl (lt_of_lt_of_le hGLt (Nat.le_add_right heap _)))).trans
          ((hs4_frame _ (lt_of_lt_of_le hGLt hHeapLeS3)
            (by rcases hSepHL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
            (by rcases hSepBL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
            ⟨Or.inr (by omega), Or.inl (by omega)⟩).trans
            ((hs3_frame _ (lt_of_lt_of_le hGLt hHeapLeS2) (hNotFoot2 hGLt (by rw [hTagMetaG j hj]; omega))
              (fun h => by have := hTagMetaG j hj; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega)
              (fun _ => ⟨by omega, by omega⟩)).trans
              (hs2_eq_mem0 (hTagMetaG j hj) (by omega) (by omega) (fun _ _ _ => by omega))))
      refine ⟨?_, ?_, fun _ => ⟨hLPtr5, hGPtr5⟩, fun h => by omega⟩
      · rw [hGPtr5, hExG j hle]
        exact dynGraphAt_of_agree hDGJ (fun a ha1 ha2 =>
          (hFrame5 a (htagLt (by rw [hTagGJ a ha1 ha2]; split_ifs <;> omega))
            (by rw [hTagGJ a ha1 ha2]; split_ifs <;> omega)
            (by rw [hTagGJ a ha1 ha2]; split_ifs <;> omega)
            (fun _ _ _ => by rw [hTagGJ a ha1 ha2]; split_ifs <;> omega)).trans
            (hmem0_eq (hTagGJ a ha1 ha2) (by split_ifs <;> omega)))
      · rw [hLPtr5, hExG j hle, shiftDeep_chainLen_le chain hiLt j hle]
        exact hLenJ.congr (fun e he t ht => by
          have heLt := hDGJ.2.2.1 e he
          have hmul : e * L + L ≤ eCap * L := by
            have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
          have ht23 := hTagLJ (mem0 (levelMeta + j) + e * L + t)
            (by dsimp only [levelMeta, lvlMTable, d]; omega)
            (by dsimp only [levelMeta, lvlMTable, d]; omega)
          exact (hFrame5 _ (htagLt (by rw [ht23]; omega)) (by rw [ht23]; omega) (by rw [ht23]; omega)
            (fun _ _ _ => by rw [ht23]; omega)).trans (hmem0_eq ht23 (by omega)))
    · by_cases hji1 : j = i0 + 1
      · subst hji1
        have hLPtr5 : s5.mem (levelMeta + (i0 + 1)) = s3.regs 7 :=
          (hs5_frame _ (lt_of_lt_of_le hMLt hHeapLeS4) (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 hMLt (by rw [hTagMetaL (i0 + 1) hj]; omega))
              (Or.inl (lt_of_lt_of_le hMLt (Nat.le_add_right heap _)))).trans
            ((hs4_frame _ (lt_of_lt_of_le hMLt hHeapLeS3)
              (by rcases hSepHL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
              (by rcases hSepBL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
              ⟨Or.inl (by omega), Or.inl (by omega)⟩).trans (hMeta3 hj).1)
        have hGPtr5 : s5.mem (levelMeta + d + (i0 + 1)) = s3.regs 6 :=
          (hs5_frame _ (lt_of_lt_of_le hGLt hHeapLeS4) (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 hGLt (by rw [hTagMetaG (i0 + 1) hj]; omega))
              (Or.inl (lt_of_lt_of_le hGLt (Nat.le_add_right heap _)))).trans
            ((hs4_frame _ (lt_of_lt_of_le hGLt hHeapLeS3)
              (by rcases hSepHL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
              (by rcases hSepBL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
              ⟨Or.inr (by omega), Or.inl (by omega)⟩).trans (hMeta3 hj).2)
        have hnf35 (a : ℕ) (haLo : s2.regs 4 ≤ a) (haHi : a < s3.regs 4)
            (hnfI : ¬ Rcore.foot (tok.coreHandle i0) yI0_3 a) :
            s5.mem a = s3.mem a ∧
            ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (next.G d).E).foot
                newTermH newTermTok a ∧
            ∀ r < d, ¬ Rcore.foot (newCoreHandle r) (newCoreTok r) a := by
          have hnf4 : ∀ r, i0 ≤ r → r < d → ¬ Rcore.foot (coreHandle4 r) (coreTok4' r) a := fun r hr1 hr2 hf => by
            by_cases hri : r = i0
            · subst hri; simp only [coreHandle4, coreTok4', ↓reduceIte] at hf; exact hnfI hf
            · simp only [coreHandle4, coreTok4', hri, ↓reduceIte] at hf
              exact absurd (lt_of_lt_of_le haHi ((hCores4 r (by omega) hr2).2.2.2.2 a hf).1) (Nat.lt_irrefl _)
          refine ⟨(hs5_frame a (haHi.trans_le hs4_lo) hnf4
                (Or.inr (le_trans (show heap + cnt + (d - i0 + 1) ≤ heap + 2 * (d - i0 + 1) by dsimp only [cnt]; omega) (le_trans hs2_lo haLo)))).trans
              (hs4_frame a haHi
                (Or.inr (lt_of_lt_of_le hH_end (le_trans hHeapLeS2 haLo)))
                (Or.inr (lt_of_lt_of_le hLevelEnd (le_trans hHeapLeS2 haLo)))
                ⟨Or.inr (le_trans (by omega) (le_trans hMetaEnd (le_trans hHeapLeS2 haLo))),
                 Or.inr (le_trans hMetaEnd (le_trans hHeapLeS2 haLo))⟩),
            fun hf => absurd (lt_of_lt_of_le haHi (hTermFoot4 a hf).1) (Nat.lt_irrefl _),
            fun r hr hf => by
              by_cases hlt : r < i0
              · simp only [newCoreHandle, newCoreTok, show r ≤ i0 by omega, hlt, ↓reduceIte] at hf
                exact absurd (lt_of_lt_of_le (hCoreFootLt r hr a hf) (le_trans hHeapLeS2 haLo)) (Nat.lt_irrefl _)
              · rw [hNewHandleGe r (by omega)] at hf; simp only [newCoreTok, hlt, ↓reduceIte] at hf
                rcases (hCores5_ico r (by omega) hr).2.2.2 a hf with h4 | ⟨hlo, _⟩
                · exact hnf4 r (by omega) hr h4
                · exact absurd (lt_of_lt_of_le (haHi.trans_le hs4_lo) hlo) (Nat.lt_irrefl _)⟩
        refine ⟨
          hGPtr5.symm ▸ dynGraphAt_of_agree hH3 (fun a ha1 ha2 =>
            (hnf35 a (le_trans h6Lo3 ha1) (lt_of_lt_of_le ha2 hHEnd3) (h6Disj3 a ha1 ha2)).1),
          hLPtr5.symm ▸ hFmtPrec ▸ (hExEll.symm ▸ hLen3).congr (fun e he t ht => by
            have heLt := hH3.2.2.1 e he
            have hmul : e * L + L ≤ eCap * L := by
              have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
            exact (hnf35 _ (le_trans h7Lo3 (by omega)) (lt_of_lt_of_le (by omega) hLenEnd3)
              (h7Disj3 _ (by omega) (by omega))).1),
          fun h => by omega,
          fun _ => ⟨by rw [hLPtr5]; exact le_trans hHeapLeS2 h7Lo3,
            by rw [hLPtr5]; exact le_trans hLenEnd3 (le_trans hs4_lo hs5_lo),
            by rw [hGPtr5]; exact le_trans hHeapLeS2 h6Lo3,
            by rw [hGPtr5]; exact le_trans hHEnd3 (le_trans hs4_lo hs5_lo),
            fun a ha1 ha2 => by rw [hLPtr5] at ha1 ha2; exact (hnf35 a (le_trans h7Lo3 ha1) (lt_of_lt_of_le ha2 hLenEnd3) (h7Disj3 a ha1 ha2)).2,
            fun a ha1 ha2 => by rw [hGPtr5] at ha1 ha2; exact (hnf35 a (le_trans h6Lo3 ha1) (lt_of_lt_of_le ha2 hHEnd3) (h6Disj3 a ha1 ha2)).2⟩⟩
      · obtain ⟨hDGJ, hGLoJ, hGHiJ, hLenJ, hLLoJ, hLHiJ, hDisjC, hDisjTL, hDisjTG⟩ :=
          hMeta4 j (by omega) hj
        have hLPtr5 : s5.mem (levelMeta + j) = s4.mem (levelMeta + j) :=
          hs5_frame _ (lt_of_lt_of_le hMLt hHeapLeS4) (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 hMLt (by rw [hTagMetaL j hj]; omega))
            (Or.inl (lt_of_lt_of_le hMLt (Nat.le_add_right heap _)))
        have hGPtr5 : s5.mem (levelMeta + d + j) = s4.mem (levelMeta + d + j) :=
          hs5_frame _ (lt_of_lt_of_le hGLt hHeapLeS4) (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 hGLt (by rw [hTagMetaG j hj]; omega))
            (Or.inl (lt_of_lt_of_le hGLt (Nat.le_add_right heap _)))
        have hnf45 (a : ℕ) (haLo : s3.regs 4 ≤ a) (haHi : a < s4.regs 4)
            (hnfR : ∀ r, i0 + 1 ≤ r → r < d → ¬ Rcore.foot (s4.mem (handleBase + r)) (coreTok4 r) a) :
            s5.mem a = s4.mem a ∧ ∀ r < d, ¬ Rcore.foot (newCoreHandle r) (newCoreTok r) a := by
          have hnf4 : ∀ r, i0 ≤ r → r < d → ¬ Rcore.foot (coreHandle4 r) (coreTok4' r) a := fun r hr1 hr2 hf => by
            by_cases hri : r = i0
            · subst hri; simp only [coreHandle4, coreTok4', ↓reduceIte] at hf
              exact absurd (lt_of_lt_of_le (hY3FootLt a hf) haLo) (Nat.lt_irrefl _)
            · simp only [coreHandle4, coreTok4', hri, ↓reduceIte] at hf; exact hnfR r (by omega) hr2 hf
          refine ⟨hs5_frame a haHi hnf4 (Or.inr (le_trans (by dsimp only [heap1]; omega) (le_trans hs3_geHeap1 haLo))),
            fun r hr hf => by
              by_cases hlt : r < i0
              · simp only [newCoreHandle, newCoreTok, show r ≤ i0 by omega, hlt, ↓reduceIte] at hf
                exact absurd (lt_of_lt_of_le (hCoreFootLt r hr a hf) (le_trans hHeapLeS3 haLo)) (Nat.lt_irrefl _)
              · rw [hNewHandleGe r (by omega)] at hf; simp only [newCoreTok, hlt, ↓reduceIte] at hf
                rcases (hCores5_ico r (by omega) hr).2.2.2 a hf with h4 | ⟨hlo, _⟩
                · exact hnf4 r (by omega) hr h4
                · exact absurd (lt_of_lt_of_le haHi hlo) (Nat.lt_irrefl _)⟩
        refine ⟨
          hGPtr5.symm ▸ dynGraphAt_of_agree hDGJ (fun a ha1 ha2 =>
            (hnf45 a (le_trans hGLoJ ha1) (lt_of_lt_of_le ha2 hGHiJ) (fun r hr1 hr2 => (hDisjC r hr1 hr2).2 a ha1 ha2)).1),
          hLPtr5.symm ▸ hFmtPrec ▸ hLenJ.congr (fun e he t ht => by
            have heLt := hDGJ.2.2.1 e he
            have hmul : e * L + L ≤ eCap * L := by
              have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
            exact (hnf45 _ (le_trans hLLoJ (by omega)) (lt_of_lt_of_le (by omega) hLHiJ)
              (fun r hr1 hr2 => (hDisjC r hr1 hr2).1 _ (by omega) (by omega))).1),
          fun h => by omega,
          fun _ => ⟨by rw [hLPtr5]; exact le_trans hHeapLeS3 hLLoJ,
            by rw [hLPtr5]; exact le_trans hLHiJ hs5_lo,
            by rw [hGPtr5]; exact le_trans hHeapLeS3 hGLoJ,
            by rw [hGPtr5]; exact le_trans hGHiJ hs5_lo,
            fun a ha1 ha2 => by
              rw [hLPtr5] at ha1 ha2
              exact ⟨hDisjTL a ha1 ha2, (hnf45 a (le_trans hLLoJ ha1) (lt_of_lt_of_le ha2 hLHiJ)
                (fun r hr1 hr2 => (hDisjC r hr1 hr2).1 a ha1 ha2)).2⟩,
            fun a ha1 ha2 => by
              rw [hGPtr5] at ha1 ha2
              exact ⟨hDisjTG a ha1 ha2, (hnf45 a (le_trans hGLoJ ha1) (lt_of_lt_of_le ha2 hGHiJ)
                (fun r hr1 hr2 => (hDisjC r hr1 hr2).2 a ha1 ha2)).2⟩⟩⟩
  · -- `hMetaOrd5` for `i0 < j < d`
    have hL5_eq4 (j : ℕ) (hj : j < d) : s5.mem (levelMeta + j) = s4.mem (levelMeta + j) :=
      hs5_frame _ (lt_of_lt_of_le (lt_of_lt_of_le (by omega) hMetaEnd) hHeapLeS4)
        (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 (lt_of_lt_of_le (by omega) hMetaEnd) (by rw [hTagMetaL j hj]; omega))
        (Or.inl (lt_of_lt_of_le (lt_of_lt_of_le (by omega) hMetaEnd) (Nat.le_add_right heap _)))
    have hG5_eq4 (j : ℕ) (hj : j < d) : s5.mem (levelMeta + d + j) = s4.mem (levelMeta + d + j) :=
      hs5_frame _ (lt_of_lt_of_le (lt_of_lt_of_le (by omega) hMetaEnd) hHeapLeS4)
        (fun r hr1 hr2 => hCellDisj4 r hr1 hr2 (lt_of_lt_of_le (by omega) hMetaEnd) (by rw [hTagMetaG j hj]; omega))
        (Or.inl (lt_of_lt_of_le (lt_of_lt_of_le (by omega) hMetaEnd) (Nat.le_add_right heap _)))
    have hL4_i1 (h1 : i0 + 1 < d) : s4.mem (levelMeta + (i0 + 1)) = s3.regs 7 :=
      (hs4_frame _ (lt_of_lt_of_le (lt_of_lt_of_le (by omega) hMetaEnd) hHeapLeS3)
        (by rcases hSepHL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
        (by rcases hSepBL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
        ⟨Or.inl (by omega), Or.inl (by omega)⟩).trans (hMeta3 h1).1
    have hG4_i1 (h1 : i0 + 1 < d) : s4.mem (levelMeta + d + (i0 + 1)) = s3.regs 6 :=
      (hs4_frame _ (lt_of_lt_of_le (lt_of_lt_of_le (by omega) hMetaEnd) hHeapLeS3)
        (by rcases hSepHL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
        (by rcases hSepBL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
        ⟨Or.inr (by omega), Or.inl (by omega)⟩).trans (hMeta3 h1).2
    refine ⟨fun j hgt hj => ?_, fun j₁ j₂ hgt hlt hj2 => ?_⟩
    · rw [hG5_eq4 j hj, hL5_eq4 j hj]
      by_cases h1 : j = i0 + 1
      · subst h1; rw [hG4_i1 hj, hL4_i1 hj]; exact h6Le7_3
      · exact hMetaOrd4.1 j (by omega) hj
    · rw [hL5_eq4 j₁ (lt_trans hlt hj2), hG5_eq4 j₂ hj2]
      by_cases h1 : j₁ = i0 + 1
      · subst h1; rw [hL4_i1 (lt_trans hlt hj2)]
        have hlo2 := (hMeta4 j₂ (by omega) hj2).2.1
        dsimp only [levelMeta, d] at hlo2 ⊢; omega
      · exact hMetaOrd4.2 j₁ j₂ (by omega) hlt hj2
  · -- Cost + `Rcore.phi` telescoping over `Fin d`
    have hPhi5 :
        (∑ j : Fin d, Rcore.phi (newCoreHandle j.val) (newCoreTok j.val) s5.mem) =
        (Finset.range i0).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0) +
        (Finset.Ico i0 d).sum (fun j => Rcore.phi (coreHandle4 j) (coreTok5 j) s5.mem) := by
      rw [sum_Fin_eq_range_plus_Ico hiLt (fun j => Rcore.phi (newCoreHandle j) (newCoreTok j) s5.mem)]
      congr 1
      · refine Finset.sum_congr rfl (fun j hj => ?_)
        have hlt := Finset.mem_range.mp hj
        simp only [newCoreHandle, newCoreTok, show j ≤ i0 by omega, hlt, ↓reduceIte]
        exact (hPreCore5 j hlt).2.2.2
      · refine Finset.sum_congr rfl (fun j hj => ?_)
        obtain ⟨hj1, _⟩ := Finset.mem_Ico.mp hj
        rw [hNewHandleGe j hj1]; simp only [newCoreTok, show ¬ j < i0 by omega, ↓reduceIte]
    have hPhi0 :
        (∑ j : Fin d, Rcore.phi (tok.coreHandle j.val) (tok.coreTok j.val) mem0) =
        (Finset.range i0).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0) +
        (Finset.Ico i0 d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0) :=
      sum_Fin_eq_range_plus_Ico hiLt (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0)
    rw [hPhi5, hPhi0]
    clear rAll hH3 hLen3 hOldForestsSafe2 hCores4 hMeta4 hTermRep4 hTermFoot4 hTermDisj4
      hCores5_ico hCoreDisj5_ico hNewForests5 hOldForests5 hPreCore5 hTermPres5 hPhi5 hPhi0
    dsimp only [d, i0, chain, next, coreHandle4, handleBase] at hc04a ⊢
    omega

/-- Re-associate `((a ;; b) ;; c)` to `(a ;; (b ;; c))`. -/
theorem runs_seq_reassoc_deep {w : ℕ} {p : Program} {ω : ℕ → Bool} {a b c : Stmt}
    {st mid out : State} {o : Outcome} {c1 c2 : ℕ}
    (h1 : Runs w p ω (a ;; b) st .normal mid c1)
    (h2 : Runs w p ω c mid o out c2) :
    Runs w p ω (a ;; (b ;; c)) st o out (c1 + c2 + 1) := by
  rcases runs_seq_iff.mp h1 with ⟨_, _, _, hne, _⟩ | ⟨s1, ca, cb, ra, rb, rfl⟩
  · exact absurd hne (by simp)
  · exact runs_seq_iff.mpr (Or.inr ⟨s1, ca, cb + c2 + 1, ra,
      runs_seq_iff.mpr (Or.inr ⟨mid, cb, c2, rb, h2, rfl⟩), by omega⟩)

/-- Base pointer of a represented `pathRep` lies inside its footprint. -/
theorem pathRep_foot_base_mem_deep {L C b : ℕ} {s : PathTreeState}
    {x : (LinkCut.PathProg.pathRep 4 L C).τ} {mem : ℕ → ℕ}
    (_hrep : (LinkCut.PathProg.pathRep 4 L C).rep b s x mem) :
    (LinkCut.PathProg.pathRep 4 L C).foot b x b := by
  refine ⟨le_rfl, ?_⟩
  unfold LinkCut.PathProg.arenaEnd LinkCut.PathProg.arenaNb LinkCut.PathProg.recW
  have h1 : 1 ≤ LinkCut.PathProg.recW (LinkCut.PathProg.treeLimbs L) := by
    unfold LinkCut.PathProg.recW; omega
  have h3 := Nat.mul_pos h1 (by omega : 0 < 2 * x.1.n + 1)
  unfold LinkCut.PathProg.recW at h3; omega

/-- Compose Phases 0–4a and the pack/sync/ret tail into `shiftDeepChainBodyKFBL`. -/
theorem shiftDeep_compose_body_runs
    {w initCore op1 op3 op2 coreLenProc op5 lastInit packEditsProc op4t op1t op0t
      bind canonCopy isNeg c04a cTail nextHeap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st s5 s11 : State}
    (r04a : Runs w p ω
      (shiftDeepInitRegsKFBL ;; shiftDeepCollectOldKFBL op2 ;;
        shiftDeepRestartAndReadoutKFBL op1 op3 op2 coreLenProc op5 ;;
        ordRebuildSuffixProgramKFBLStore initCore op3 op2 coreLenProc op5 lastInit ;;
        (.assign 20 (.reg 71) ;; collectLSFForestsLoop op2 81 ;; collectTermForestStmt 81))
      st .normal s5 c04a)
    (rTail : Runs w p ω
      (.assign 10 (.load (.bin .add (.reg 70) (.const 15))) ;;
       .assign 6 (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 10))) ;;
       .call 18 packEditsProc [.reg 80, .reg 81, .reg 79, .reg 10, .reg 4] ;;
       .assign 27 (.reg 70) ;; .assign 29 (.reg 73) ;;
       shiftTermSetupLoop ;;
       wireTreeSyncLoop op4t op1t op0t bind canonCopy isNeg ;;
       .ret (.reg 3))
      s5 (.returned nextHeap) s11 cTail) :
    Runs w p ω
      (shiftDeepChainBodyKFBL initCore op1 op3 op2 coreLenProc op5 lastInit packEditsProc
        op4t op1t op0t bind canonCopy isNeg)
      st (.returned nextHeap) s11 (c04a + cTail + 1) := by
  rcases runs_seq_iff.mp r04a with ⟨_, _, _, hne, _⟩ | ⟨t1, ca, c1', ra, r1', hc1'⟩
  · exact absurd hne (by simp)
  · rcases runs_seq_iff.mp r1' with ⟨_, _, _, hne, _⟩ | ⟨t2, cb, c2', rb, r2', hc2'⟩
    · exact absurd hne (by simp)
    · rcases runs_seq_iff.mp r2' with ⟨_, _, _, hne, _⟩ | ⟨t3, cc, c3', rc, r3', hc3'⟩
      · exact absurd hne (by simp)
      · rcases runs_seq_iff.mp r3' with ⟨_, _, _, hne, _⟩ | ⟨t4, cd, ce, rd, re, hc4'⟩
        · exact absurd hne (by simp)
        · have rPhase4 : Runs w p ω
              (shiftDeepCollectNewAndSync op2 packEditsProc op4t op1t op0t bind canonCopy isNeg)
              t4 (.returned nextHeap) s11 (ce + cTail + 1) := by
            rcases runs_seq_iff.mp re with ⟨_, _, _, hne, _⟩ | ⟨u1, ce1, ce2, re1, re2, hce⟩
            · exact absurd hne (by simp)
            · exact runs_seq_iff.mpr (Or.inr ⟨u1, ce1, _, re1, runs_seq_reassoc_deep re2 rTail, by omega⟩)
          exact runs_seq_iff.mpr (Or.inr ⟨t1, ca, _, ra,
            runs_seq_iff.mpr (Or.inr ⟨t2, cb, _, rb,
            runs_seq_iff.mpr (Or.inr ⟨t3, cc, _, rc,
            runs_seq_iff.mpr (Or.inr ⟨t4, cd, _, rd, rPhase4, rfl⟩), rfl⟩), rfl⟩), by omega⟩)

end MinCostFlow.MinRatio
