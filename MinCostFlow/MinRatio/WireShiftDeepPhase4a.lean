module

public import MinCostFlow.MinRatio.WireShiftDeepPhase3
import WordRAM.Tactic

/-!
# Deep shift Phases 0–4a execution (`WireShiftDeepPhase4a`)

Composes `shiftDeep_phases_0_to_3_runs` (`WireShiftDeepPhase3.lean`) with Phase 4a
(`shiftDeepCollectNewKFBL_runs`) under the layout contract, exposing the raw post-Phase-4a state `s5`, new suffix forests,
updated cores on `[i0, d)`, frame, and cost bound for assembly in `WireShiftDeepAux.lean`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program Bundle

set_option maxHeartbeats 800000 in
/-- Raw execution of Phases 0–4a of `shiftDeepChainBodyKFBL` on a non-terminal shift `i < d`. -/
theorem shiftDeep_phases_0_to_4a_raw
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
    let i0 := i.val
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i0).1
    let handleBase := tok.handle + 18
    let branchBase := handleBase + (d + 1)
    let levelMeta := solverLevelMetaAddr tok.table d
    let cnt := d - i0 + 1
    let heap1 := heap + 2 * cnt
    let forestSafe : ℕ → Prop := fun a =>
      (a < heap → tok.tag a ≠ 4 ∧ tok.tag a ≠ 22 + d) ∧ (a < heap ∨ heap1 ≤ a)
    let phase04a : Stmt :=
      shiftDeepInitRegsKFBL ;;
      shiftDeepCollectOldKFBL (opCore 2) ;;
      shiftDeepRestartAndReadoutKFBL (opCore 1) (opCore 3) (opCore 2) coreLenProc (opCore 5) ;;
      ordRebuildSuffixProgramKFBLStore initCore (opCore 3) (opCore 2) coreLenProc (opCore 5)
        lastInit ;;
      (.assign 20 (.reg 71) ;; collectLSFForestsLoop (opCore 2) 81 ;; collectTermForestStmt 81)
    ∃ (s2 s3 s4 s5 : State) (c04a newTermTok : ℕ)
      (yI0_2 yI0_3 : Rcore.τ) (coreTok4 coreTok5 : ℕ → Rcore.τ),
      let coreHandle4 : ℕ → ℕ := fun j => if j = i0 then tok.coreHandle i0 else s4.mem (handleBase + j)
      let coreTok4' : ℕ → Rcore.τ := fun j => if j = i0 then yI0_3 else coreTok4 j
      Runs w p ω phase04a (startState [root, i0, heap] mem pos) .normal s5 c04a ∧
      heap1 ≤ s2.regs 4 ∧ s2.regs 4 ≤ s3.regs 4 ∧ s3.regs 4 ≤ s4.regs 4 ∧ s4.regs 4 ≤ s5.regs 4 ∧
      s5.regs 4 + 3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L) ≤ heap + deepSpace ∧
      ZeroFrom s5.mem (s5.regs 4) ∧
      -- Phase 1 old forests + frame
      (∀ t (ht : t < (chainSuffixForests model.chain i0).length),
        ∃ vc ec,
          DynGraphAt s2.mem (s2.mem (heap + t)) vc ec (chainSuffixForests model.chain i0)[t] ∧
          s2.mem (heap + t) + dynGraphSize vc ec ≤ s2.regs 4 ∧
          (∀ e ∈ (chainSuffixForests model.chain i0)[t].E, e < tok.intCap) ∧
          (∀ a, s2.mem (heap + t) ≤ a → a < s2.mem (heap + t) + dynGraphSize vc ec →
            ¬ Rcore.foot (tok.coreHandle i0) yI0_2 a ∧ forestSafe a)) ∧
      (∀ a, Rcore.foot (tok.coreHandle i0) yI0_2 a →
        Rcore.foot (tok.coreHandle i0) (tok.coreTok i0) a ∨ (heap1 ≤ a ∧ a < s2.regs 4)) ∧
      (∀ a < heap1,
        (∀ j, i0 ≤ j → j < d → ¬ Rcore.foot (tok.coreHandle j) (tok.coreTok j) a) →
        (a < heap ∨ heap + cnt ≤ a) → s2.mem a = mem a) ∧
      -- Phase 2 outputs + frame
      s3.mem (branchBase + i0) = (model.chain.bran i0 + 1) % cfg.P.k ∧
      (∀ a, Rcore.foot (tok.coreHandle i0) yI0_3 a →
        Rcore.foot (tok.coreHandle i0) yI0_2 a ∨ (s2.regs 4 ≤ a ∧ a < s3.regs 4)) ∧
      DynGraphAt s3.mem (s3.regs 6) vCap eCap (next.G (i0 + 1)) ∧
      EdgeValuesAt s3.mem (s3.regs 7) 4 L fmt.precision (next.G (i0 + 1)).E
        (next.toTreeChain.chainLen model.chain.ℓ (i0 + 1)) ∧
      s2.regs 4 ≤ s3.regs 6 ∧ s3.regs 6 + dynGraphSize vCap eCap ≤ s3.regs 4 ∧
      (∀ a, s3.regs 6 ≤ a → a < s3.regs 6 + dynGraphSize vCap eCap →
        ¬ Rcore.foot (tok.coreHandle i0) yI0_3 a) ∧
      s2.regs 4 ≤ s3.regs 7 ∧ s3.regs 7 + eCap * L ≤ s3.regs 4 ∧
      (∀ a, s3.regs 7 ≤ a → a < s3.regs 7 + eCap * L →
        ¬ Rcore.foot (tok.coreHandle i0) yI0_3 a) ∧
      s3.regs 6 + dynGraphSize vCap eCap ≤ s3.regs 7 ∧
      (i0 + 1 < d → s3.mem (levelMeta + (i0 + 1)) = s3.regs 7 ∧
        s3.mem (levelMeta + d + (i0 + 1)) = s3.regs 6) ∧
      (∀ a < s2.regs 4, ¬ Rcore.foot (tok.coreHandle i0) yI0_2 a →
        a ≠ branchBase + i0 →
        (i0 + 1 < d → a ≠ levelMeta + (i0 + 1) ∧ a ≠ levelMeta + d + (i0 + 1)) →
        s3.mem a = s2.mem a) ∧
      -- Phase 3 outputs + frame
      (∀ j, i0 + 1 ≤ j → j < d →
        s4.mem (branchBase + j) = next.bran j ∧
        s3.regs 4 ≤ s4.mem (handleBase + j) ∧ s4.mem (handleBase + j) ≤ s4.regs 4 ∧
        Rcore.rep (s4.mem (handleBase + j)) (chainLevelOrdAbs next j) (coreTok4 j) s4.mem ∧
        (∀ a, Rcore.foot (s4.mem (handleBase + j)) (coreTok4 j) a →
          s3.regs 4 ≤ a ∧ a < s4.regs 4)) ∧
      (∀ j, i0 + 1 + 1 ≤ j → j < d →
        DynGraphAt s4.mem (s4.mem (levelMeta + d + j)) vCap eCap (next.G j) ∧
        s3.regs 4 ≤ s4.mem (levelMeta + d + j) ∧
        s4.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ s4.regs 4 ∧
        EdgeValuesAt s4.mem (s4.mem (levelMeta + j)) 4 L fmt.precision (next.G j).E
          (next.toTreeChain.chainLen next.ℓ j) ∧
        s3.regs 4 ≤ s4.mem (levelMeta + j) ∧
        s4.mem (levelMeta + j) + eCap * L ≤ s4.regs 4 ∧
        (∀ r, i0 + 1 ≤ r → r < d →
          (∀ a, s4.mem (levelMeta + j) ≤ a → a < s4.mem (levelMeta + j) + eCap * L →
            ¬ Rcore.foot (s4.mem (handleBase + r)) (coreTok4 r) a) ∧
          (∀ a, s4.mem (levelMeta + d + j) ≤ a →
            a < s4.mem (levelMeta + d + j) + dynGraphSize vCap eCap →
            ¬ Rcore.foot (s4.mem (handleBase + r)) (coreTok4 r) a)) ∧
        (∀ a, s4.mem (levelMeta + j) ≤ a → a < s4.mem (levelMeta + j) + eCap * L →
          ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
              (next.G d).E).foot (s4.mem (handleBase + d)) newTermTok a) ∧
        (∀ a, s4.mem (levelMeta + d + j) ≤ a →
          a < s4.mem (levelMeta + d + j) + dynGraphSize vCap eCap →
          ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
              (next.G d).E).foot (s4.mem (handleBase + d)) newTermTok a)) ∧
      ((∀ j, i0 + 1 + 1 ≤ j → j < d →
          s4.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ s4.mem (levelMeta + j)) ∧
       (∀ j₁ j₂, i0 + 1 + 1 ≤ j₁ → j₁ < j₂ → j₂ < d →
          s4.mem (levelMeta + j₁) + eCap * L ≤ s4.mem (levelMeta + d + j₂))) ∧
      s4.mem (branchBase + d) = next.lastBran ∧
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision (next.G d).E).rep
        (s4.mem (handleBase + d)) (next.lastK, next.lastLSFs) newTermTok s4.mem ∧
      (∀ a, (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
          (next.G d).E).foot (s4.mem (handleBase + d)) newTermTok a →
        s3.regs 4 ≤ a ∧ a < s4.regs 4) ∧
      (∀ j, i0 + 1 ≤ j → j < d →
        ∀ a, (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
            (next.G d).E).foot (s4.mem (handleBase + d)) newTermTok a →
          ¬ Rcore.foot (s4.mem (handleBase + j)) (coreTok4 j) a) ∧
      (∀ a < s3.regs 4,
        (a < handleBase + (i0 + 1) ∨ handleBase + d < a) →
        (a < branchBase + (i0 + 1) ∨ branchBase + d < a) →
        ((a < levelMeta + (i0 + 1 + 1) ∨ levelMeta + d ≤ a) ∧
         (a < levelMeta + d + (i0 + 1 + 1) ∨ levelMeta + 2 * d ≤ a)) →
        s4.mem a = s3.mem a) ∧
      -- Phase 4a outputs + frame + registers + cost
      ForestPtrListAt s5.mem (heap + cnt) (chainSuffixForests next i0) tok.intCap (s5.regs 4) ∧
      (∀ j, i0 ≤ j → j < d →
        s4.mem (handleBase + j) = coreHandle4 j ∧
        s4.mem (branchBase + j) = next.bran j ∧
        Rcore.rep (coreHandle4 j) (chainLevelOrdAbs next j) (coreTok5 j) s5.mem ∧
        (∀ a, Rcore.foot (coreHandle4 j) (coreTok5 j) a →
          Rcore.foot (coreHandle4 j) (coreTok4' j) a ∨ (s4.regs 4 ≤ a ∧ a < s5.regs 4))) ∧
      (∀ j₁ j₂, i0 ≤ j₁ → j₁ < d → i0 ≤ j₂ → j₂ < d → j₁ ≠ j₂ →
        ∀ a, Rcore.foot (coreHandle4 j₁) (coreTok5 j₁) a →
          ¬ Rcore.foot (coreHandle4 j₂) (coreTok5 j₂) a) ∧
      (∀ a < s4.regs 4,
        (∀ j, i0 ≤ j → j < d → ¬ Rcore.foot (coreHandle4 j) (coreTok4' j) a) →
        (a < heap + cnt ∨ heap + cnt + cnt ≤ a) → s5.mem a = s4.mem a) ∧
      s5.regs 70 = root ∧ s5.regs 71 = i0 ∧ s5.regs 73 = tok.handle ∧
      s5.regs 75 = d ∧ s5.regs 79 = cnt ∧ s5.regs 80 = heap ∧ s5.regs 81 = heap + cnt ∧
      c04a + (Finset.Ico i0 d).sum (fun j => Rcore.phi (coreHandle4 j) (coreTok5 j) s5.mem) +
        85 * (graphListEdgeSum (chainSuffixForests model.chain i0) +
          graphListEdgeSum (chainSuffixForests next i0)) + 210 * (d + 1) + 400 ≤
        deepFixed + toolMul * (next.totalRuntime - model.chain.totalRuntime) +
          (Finset.Ico i0 d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0) := by
  dsimp only
  let d := cfg.P.d
  let i0 := i.val
  let chain := model.chain
  let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P chain i0).1
  have hChain' : (alg2LoopShiftStep cfg model i).chain = next := by
    simp [alg2LoopShiftStep, next, chain, i0]
  let handleBase := tok.handle + 18
  let branchBase := handleBase + (d + 1)
  let lvlMTable := solverLvlMAddr tok.table d
  let levelMeta := solverLevelMetaAddr tok.table d
  let cnt := d - i0 + 1
  let heap1 := heap + 2 * cnt
  -- Run Phases 0–3
  obtain ⟨s2, s3, s4, c03, newTermTok, yI0_2, yI0_3, coreTok4,
      r03, hs2_lo, h4Lo3, hs4_lo, hs4_heapLe, hz4, hOldForestsSafe2, hFootI0_2, hs2_frame,
      hBr3, hFootI0_3, hH3, hLen3, h6Lo3, hHEnd3, h6Disj3, h7Lo3, hLenEnd3, h7Disj3, h6Le7_3, hMeta3,
      hs3_frame, hY3Rep4, hY3Phi4, hCores4, hCoreDisj4, hMeta4, hMetaOrd4, hTermB4, hTermRep4, hTermFoot4,
      hTermDisj4, hs4_frame, h4_70, h4_71, h4_73, h4_75, h4_77, h4_78, h4_79, h4_80, h4_81,
      h4_83, hc03⟩ :=
    shiftDeep_phases_0_to_3_runs (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi)
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
  -- Unpack needed facts and clear heavy unused hypotheses
  obtain ⟨_, _, _, _, hFresh0, _, hExtM0, ⟨hG0Cap, _, _, _⟩, _, _, _, _, _, _, hCores0, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, _, _, _, hT4, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT21⟩ := hTags0
  have hMetaCaps := SolverLevelMetaAt.atCaps hMeta0 hCaps0
  have hLvlN := hModelK.2.1
  rw [hChain'] at hLvlN
  have hCoreNext : ∀ j < cfg.P.d,
      SparseCoreReadoutFootAt fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T (next.G j) cfg.P.k
        (next.lvlM j) next.N₀ vCap eCap capExp Psc allocation Rcore p opCore := by
    intro j hj
    rw [hLvlN.2.1, hLvlN.2.2.1]
    have hM0_le_m : (next.G 0).m ≤ m := by
      have hG0Eq : next.G 0 = model.chain.G 0 :=
        (ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P chain hiLt).1 0 (Nat.zero_le _)
      rw [hG0Eq, hFresh0.m_eq]
      exact (Finset.card_le_card fun e he => Finset.mem_range.mpr (hExtM0 e he)).trans_eq
        (Finset.card_range m)
    exact (hCore j hj (next.G j) (hLvlN.1 j (le_of_lt hj))
      ((hLvlN.2.2.2 j (le_of_lt hj)).trans hM0_le_m)).2
  obtain ⟨_, hCoreOwn0, _, _, hTagMeta0, _⟩ := hMeta0
  obtain ⟨⟨_, hNextLastKPos⟩, hScIn0, _, _, _, hNextLvls, _, _, _, _, _, _, hLsfSub, _, hLastSubNew, _⟩ := hModelInv
  clear hLastImpl hCoreLenProc hEdgeProc hSign hMul hDiv hCopy hInitOrdEq
  obtain ⟨hExG, _, hExSc, hExBr, hExUpd, _, _, _, hExLvls, _, hExLastBr, _, _,
      hExEll, _, hExLvlM, hExN0⟩ := ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P chain hiLt
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
  have hNotFoot2 {a : ℕ} (ha : a < heap) (hne : tok.tag a ≠ 21 + i0) :
      ¬ Rcore.foot (tok.coreHandle i0) yI0_2 a := fun hf => by
    rcases hFootI0_2 a hf with h0 | ⟨hlo, _⟩
    · exact hne (hT21 i0 hiLt a h0)
    · exact absurd (lt_of_lt_of_le ha (le_trans (Nat.le_add_right heap _) hlo)) (Nat.lt_irrefl _)
  have hs2_eq_mem0 {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv5 : v ≠ 5)
      (hvC : ∀ j, i0 ≤ j → j < d → v ≠ 21 + j) : s2.mem a = mem0 a := by
    have hlt := htagLt (ht ▸ hv0)
    rw [hs2_frame a (lt_of_lt_of_le hlt (Nat.le_add_right heap _))
      (fun j hj1 hj2 hf => hvC j hj1 hj2 (ht.symm.trans (hT21 j hj2 a hf))) (Or.inl hlt), hmem0_eq ht hv5]
  have hs3_eq_mem0 {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv4 : v ≠ 4) (hv5 : v ≠ 5)
      (hv22 : v ≠ 22 + d) (hvC : ∀ j, i0 ≤ j → j < d → v ≠ 21 + j) : s3.mem a = mem0 a := by
    have hlt := htagLt (ht ▸ hv0)
    rw [hs3_frame a (lt_of_lt_of_le hlt (le_trans (Nat.le_add_right heap _) hs2_lo))
      (hNotFoot2 hlt (ht ▸ hvC i0 le_rfl hiLt))
      (fun h => hv4 (ht.symm.trans (h ▸ hTagBranch i0 (le_of_lt hiLt))))
      (fun hlt1 => ⟨fun h => hv22 (ht.symm.trans (h ▸ hTagMetaL (i0 + 1) hlt1)),
        fun h => hv22 (ht.symm.trans (h ▸ hTagMetaG (i0 + 1) hlt1))⟩)]
    exact hs2_eq_mem0 ht hv0 hv5 hvC
  have hs3_geHeap1 : heap1 ≤ s3.regs 4 := hs2_lo.trans h4Lo3
  have hHeapLeS4 : heap ≤ s4.regs 4 := le_trans (Nat.le_add_right heap _) (le_trans hs3_geHeap1 hs4_lo)
  have hSpaceTot := hOps.spaceTotal
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
  have hY3FootLt (a : ℕ) (ha : Rcore.foot (tok.coreHandle i0) yI0_3 a) : a < s3.regs 4 := by
    rcases hFootI0_3 a ha with h2 | ⟨_, hhi⟩
    · rcases hFootI0_2 a h2 with h0 | ⟨_, hhi2⟩
      · exact (hCoreFootLt i0 hiLt a h0).trans_le (le_trans (Nat.le_add_right heap _) hs3_geHeap1)
      · exact hhi2.trans_le h4Lo3
    · exact hhi
  -- Phase 4a: `shiftDeepCollectNew` on `[i0, d]`
  let coreHandle4 : ℕ → ℕ := fun j => if j = i0 then tok.coreHandle i0 else s4.mem (handleBase + j)
  let coreTok4' : ℕ → Rcore.τ := fun j => if j = i0 then yI0_3 else coreTok4 j
  set newTermH := s4.mem (handleBase + d)
  have hNewTermRep : (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
      (next.G d).E).rep newTermH (next.lastK, next.lastLSFs) newTermTok s4.mem := hTermRep4
  have hNewTermKLt : next.lastBran < next.lastK := by rw [hExLastBr, ← hChain']; exact hNextLastKPos
  obtain ⟨hNewTermBW, hNewTermLSF⟩ := hNewTermRep.2.2.2 next.lastBran hNewTermKLt
  set newTermLsfHdr := s4.mem (newTermH + 1 + next.lastBran)
  set newTermFPtr := s4.mem (newTermLsfHdr + 1)
  have hTermFootGe3 (a : ℕ) (ha1 : newTermH ≤ a) (ha2 : a < newTermTok) : s3.regs 4 ≤ a ∧ a < s4.regs 4 :=
    hTermFoot4 a ⟨ha1, ha2⟩
  obtain ⟨hGI0, _, _, _, hTagGI0⟩ := hMetaCaps i0 hiLt
  have hGI0_end : mem0 (levelMeta + d + i0) + dynGraphSize vCap eCap ≤ heap := by
    have hpos : 0 < dynGraphSize vCap eCap := by unfold dynGraphSize; omega
    have h1 : mem0 (levelMeta + d + i0) ≤ mem0 (levelMeta + d + i0) + dynGraphSize vCap eCap - 1 := by omega
    have h2 : mem0 (levelMeta + d + i0) + dynGraphSize vCap eCap - 1 <
        mem0 (levelMeta + d + i0) + dynGraphSize vCap eCap := by omega
    have h3 := htagLt (by rw [hTagGI0 _ h1 h2]; split_ifs <;> omega)
    dsimp only [levelMeta, lvlMTable, d, i0] at h3 ⊢; omega
  have hCellDisj4 (r : ℕ) (hr1 : i0 ≤ r) (hr2 : r < d) {a : ℕ} (ha : a < heap)
      (hnt : tok.tag a ≠ 21 + i0) : ¬ Rcore.foot (coreHandle4 r) (coreTok4' r) a := by
    by_cases hri : r = i0
    · subst hri; simp only [coreHandle4, coreTok4', ↓reduceIte]
      intro hf; rcases hFootI0_3 a hf with h2 | ⟨hlo, _⟩
      · exact hNotFoot2 ha hnt h2
      · exact absurd (lt_of_lt_of_le ha (le_trans (Nat.le_add_right heap _) (le_trans hs2_lo hlo))) (Nat.lt_irrefl _)
    · simp only [coreHandle4, coreTok4', hri, ↓reduceIte]
      intro hf; have := (hCores4 r (by omega) hr2).2.2.2.2 a hf
      exact absurd (lt_of_lt_of_le ha (le_trans (Nat.le_add_right heap _) (le_trans hs3_geHeap1 this.1))) (Nat.lt_irrefl _)
  have hCores4All : ∀ j, i0 ≤ j → j < d →
      s4.mem (handleBase + j) = coreHandle4 j ∧
      s4.mem (branchBase + j) = next.bran j ∧
      next.bran j < cfg.P.k ∧ coreHandle4 j < 2 ^ w ∧
      Rcore.rep (coreHandle4 j) (chainLevelOrdAbs next j) (coreTok4' j) s4.mem ∧
      SparseCoreOrdInput cfg.T cfg.P.k (next.lvlM j) next.N₀ (next.scState j) (next.G j)
        (next.levelOrd j) (next.updCount j) ∧
      (∀ a, Rcore.foot (coreHandle4 j) (coreTok4' j) a → a < s4.regs 4) ∧
      (∀ r, i0 ≤ r → r < d →
        ¬ Rcore.foot (coreHandle4 r) (coreTok4' r) (handleBase + j) ∧
        ¬ Rcore.foot (coreHandle4 r) (coreTok4' r) (branchBase + j) ∧
        ¬ Rcore.foot (coreHandle4 r) (coreTok4' r) (levelMeta + d + j)) ∧
      (handleBase + j < heap + cnt ∨ heap + cnt + cnt ≤ handleBase + j) ∧
      (branchBase + j < heap + cnt ∨ heap + cnt + cnt ≤ branchBase + j) ∧
      (levelMeta + d + j < heap + cnt ∨ heap + cnt + cnt ≤ levelMeta + d + j) ∧
      (∀ t < cnt, ¬ Rcore.foot (coreHandle4 j) (coreTok4' j) (heap + cnt + t)) ∧
      (DynGraphAt s4.mem (s4.mem (levelMeta + d + j)) vCap eCap (next.G j) ∧
        s4.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ s4.regs 4 ∧
        (∀ a, s4.mem (levelMeta + d + j) ≤ a →
          a < s4.mem (levelMeta + d + j) + dynGraphSize vCap eCap →
          (∀ r, i0 ≤ r → r < d → ¬ Rcore.foot (coreHandle4 r) (coreTok4' r) a) ∧
          (a < heap + cnt ∨ heap + cnt + cnt ≤ a))) := by
    intro j hj1 hj2
    by_cases hji : j = i0
    · subst hji
      simp only [coreHandle4, coreTok4', ↓reduceIte]
      have hH4i : s4.mem (handleBase + i0) = tok.coreHandle i0 :=
        (hs4_frame _ (lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left hiLt handleBase) (le_of_lt hH_end))
            (le_trans (Nat.le_add_right heap _) hs3_geHeap1)) (Or.inl (by omega))
          (by rcases hSepHB with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
          (by rcases hSepHL with h | h
              · dsimp only [levelMeta, d] at h ⊢; exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
              · dsimp only [levelMeta, d] at h ⊢; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩)).trans
          ((hs3_frame _ (lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left hiLt handleBase) (le_of_lt hH_end))
              (le_trans (Nat.le_add_right heap _) hs2_lo))
            (hNotFoot2 (htagLt (by rw [hTagHandle i0 (le_of_lt hiLt)]; decide)) (by rw [hTagHandle i0 (le_of_lt hiLt)]; omega))
            (by dsimp [branchBase]; omega)
            (fun hlt => ⟨fun h => by have := hTagHandle i0 (le_of_lt hiLt); rw [h, hTagMetaL (i0 + 1) hlt] at this; omega,
              fun h => by have := hTagHandle i0 (le_of_lt hiLt); rw [h, hTagMetaG (i0 + 1) hlt] at this; omega⟩)).trans
            ((hs2_eq_mem0 (hTagHandle i0 (le_of_lt hiLt)) (by decide) (by decide) (fun _ _ _ => by omega)).trans (hCores0 i0 hiLt).1))
      have hB4i : s4.mem (branchBase + i0) = next.bran i0 :=
        (hs4_frame _ (lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left hiLt branchBase) (le_of_lt hLevelEnd))
            (le_trans (Nat.le_add_right heap _) hs3_geHeap1))
          (by rcases hSepHB with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)]) (Or.inl (by omega))
          (by rcases hSepBL with h | h
              · dsimp only [levelMeta, d] at h ⊢; exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
              · dsimp only [levelMeta, d] at h ⊢; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩)).trans
          (hBr3.trans hExBr.symm)
      have hInNextI : SparseCoreOrdInput cfg.T cfg.P.k (next.lvlM i0) next.N₀ (next.scState i0)
          (next.G i0) (next.levelOrd i0) (next.updCount i0) := by
        have hAbsEq := (ordAlgorithm1_shift_levelOrdAbs_le cfg.T cfg.L cfg.P chain hiLt).2
        unfold chainLevelOrdAbs at hAbsEq
        have h3 : next.levelOrd i0 = chain.levelOrd i0 := by injection hAbsEq
        rw [hExLvlM, hExN0, hExSc, hExG i0 le_rfl, h3, hExUpd]
        exact SparseCoreOrdInput.restart (hScIn0 i0 le_rfl hiLt) _ (Nat.mod_lt _ hkPos)
      have hGP4 : s4.mem (levelMeta + d + i0) = mem0 (levelMeta + d + i0) :=
        (hs4_frame _ (lt_of_lt_of_le (lt_of_lt_of_le (by omega : levelMeta + d + i0 < levelMeta + 2 * d) hMetaEnd)
            (le_trans (Nat.le_add_right heap _) hs3_geHeap1))
          (by rcases hSepHL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
          (by rcases hSepBL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
          ⟨Or.inr (by dsimp only [levelMeta, d]; omega), Or.inl (by dsimp only [levelMeta, d]; omega)⟩).trans
          ((hs3_frame _ (lt_of_lt_of_le (lt_of_lt_of_le (by omega : levelMeta + d + i0 < levelMeta + 2 * d) hMetaEnd)
              (le_trans (Nat.le_add_right heap _) hs2_lo))
            (hNotFoot2 (htagLt (by rw [hTagMetaG i0 hiLt]; omega)) (by rw [hTagMetaG i0 hiLt]; omega))
            (fun h => by have := hTagMetaG i0 hiLt; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega)
            (fun _ => ⟨by dsimp only [levelMeta, d]; omega, by dsimp only [levelMeta, d]; omega⟩)).trans
            (hs2_eq_mem0 (hTagMetaG i0 hiLt) (by omega) (by omega) (fun _ _ _ => by omega)))
      refine ⟨hH4i, hB4i, hExBr.symm ▸ Nat.mod_lt _ hkPos,
        lt_trans (hFootLt (tok.coreHandle i0) (Or.inl (hCoreOwn0 i0 hiLt))) (lt_of_le_of_lt (Nat.le_add_right heap _) hHeapRoom),
        hY3Rep4, hInNextI, fun a ha => (hY3FootLt a ha).trans_le hs4_lo,
        fun r hr1 hr2 => ⟨hCellDisj4 r hr1 hr2 (htagLt (by rw [hTagHandle i0 (le_of_lt hiLt)]; decide))
            (by rw [hTagHandle i0 (le_of_lt hiLt)]; omega),
          hCellDisj4 r hr1 hr2 (htagLt (by rw [hTagBranch i0 (le_of_lt hiLt)]; decide))
            (by rw [hTagBranch i0 (le_of_lt hiLt)]; omega),
          hCellDisj4 r hr1 hr2 (htagLt (by rw [hTagMetaG i0 hiLt]; omega))
            (by rw [hTagMetaG i0 hiLt]; omega)⟩,
        Or.inl (lt_of_lt_of_le (lt_trans (Nat.add_lt_add_left hiLt handleBase) hH_end) (Nat.le_add_right heap _)),
        Or.inl (lt_of_lt_of_le (lt_trans (Nat.add_lt_add_left hiLt branchBase) hLevelEnd) (Nat.le_add_right heap _)),
        Or.inl (lt_of_lt_of_le (lt_of_lt_of_le (by omega : levelMeta + d + i0 < levelMeta + 2 * d) hMetaEnd) (Nat.le_add_right heap _)),
        fun t ht hf => by
          rcases hFootI0_3 _ hf with h2 | ⟨hlo, _⟩
          · rcases hFootI0_2 _ h2 with h0 | ⟨hlo2, _⟩
            · exact absurd (lt_of_lt_of_le (hCoreFootLt i0 hiLt _ h0)
                (Nat.le_trans (Nat.le_add_right heap cnt) (Nat.le_add_right (heap + cnt) t))) (Nat.lt_irrefl _)
            · have : heap + cnt + t < heap + 2 * (d - i0 + 1) := by dsimp only [cnt]; omega
              exact absurd (lt_of_lt_of_le this hlo2) (Nat.lt_irrefl _)
          · have : heap + cnt + t < heap1 := by dsimp only [heap1]; omega
            exact absurd (lt_of_lt_of_le this (le_trans hs2_lo hlo)) (Nat.lt_irrefl _),
        ⟨by
          rw [hGP4, hExG i0 le_rfl]
          exact dynGraphAt_of_agree hGI0 (fun a ha1 ha2 => by
            have htG := hTagGI0 a ha1 ha2
            have hmG := not_mem_interval_of_tag_ne (b := levelMeta) (lo := 0) (hi := 2 * d)
              (fun k _ hk => hTagMeta0 k hk) (by rw [htG]; split_ifs <;> omega)
            exact (hs4_frame a (lt_of_lt_of_le (htagLt (by rw [htG]; split_ifs <;> omega)) (le_trans (Nat.le_add_right heap _) hs3_geHeap1))
              ((not_mem_interval_of_tag_ne (b := handleBase) (lo := i0 + 1) (hi := d + 1)
                (fun k _ hk => hTagHandle k (Nat.lt_succ_iff.mp hk)) (by rw [htG]; split_ifs <;> omega)).imp id Nat.lt_of_succ_le)
              ((not_mem_interval_of_tag_ne (b := branchBase) (lo := i0 + 1) (hi := d + 1)
                (fun k _ hk => hTagBranch k (Nat.lt_succ_iff.mp hk)) (by rw [htG]; split_ifs <;> omega)).imp id Nat.lt_of_succ_le)
              (hmG.elim
                (fun h => by dsimp only [levelMeta, d] at h ⊢; exact ⟨Or.inl (by omega), Or.inl (by omega)⟩)
                (fun h => by dsimp only [levelMeta, d] at h ⊢; exact ⟨Or.inr (by omega), Or.inr h⟩))).trans
              (hs3_eq_mem0 htG (by split_ifs <;> omega) (by split_ifs <;> omega) (by split_ifs <;> omega) (by split_ifs <;> omega) (fun _ _ _ => by split_ifs <;> omega))),
          by rw [hGP4]; exact hGI0_end.trans hHeapLeS4,
          fun a ha1 ha2 => by
            rw [hGP4] at ha1 ha2
            exact ⟨fun r hr1 hr2 => hCellDisj4 r hr1 hr2 (htagLt (by rw [hTagGI0 a ha1 ha2]; split_ifs <;> omega))
                (by rw [hTagGI0 a ha1 ha2]; split_ifs <;> omega),
              Or.inl (lt_of_lt_of_le (htagLt (by rw [hTagGI0 a ha1 ha2]; split_ifs <;> omega)) (Nat.le_add_right heap _))⟩⟩⟩
    · simp only [coreHandle4, coreTok4', hji, ↓reduceIte]
      obtain ⟨hBrJ, hHLoJ, hHHiJ, hRepJ, hFootJ⟩ := hCores4 j (by omega) hj2
      obtain ⟨hScJ, _, hBrNJ, hUpdNJ, _, _⟩ := hExLvls j (by omega) hj2
      have hNLJ := hNextLvls j (by omega) hj2
      rw [hChain'] at hNLJ
      obtain ⟨hmLeJ, hnLeJ, _, _, hRotJ, hPosJ, _, _⟩ := hNLJ
      have hValidJ : (next.G j).IsValid := by
        by_cases hji1 : j = i0 + 1
        · subst hji1; exact hH3.1
        · obtain ⟨hDGJ, _⟩ := hMeta4 j (by omega) hj2; exact hDGJ.1
      have hInNextJ : SparseCoreOrdInput cfg.T cfg.P.k (next.lvlM j) next.N₀ (next.scState j)
          (next.G j) (next.levelOrd j) (next.updCount j) := by
        rw [hScJ, hUpdNJ, hExLvlM, hExN0]
        exact SparseCoreOrdInput.init (next.G j) (next.toTreeChain.chainLen chain.ℓ j)
          (next.toTreeChain.chainGrad chain.g j) (next.levelOrd j) hValidJ
          (hExLvlM ▸ hmLeJ) (hExN0 ▸ hnLeJ) (by rw [← hExEll]; exact hPosJ) hRotJ
      have hS4LtW : s4.regs 4 < 2 ^ w := by
        clear r03 hH3 hLen3 hOldForestsSafe2 hCores4 hMeta4 hTermRep4 hc03 hInNextJ hValidJ
        omega
      refine ⟨trivial, hBrJ, by rw [hBrNJ]; exact hkPos, lt_of_le_of_lt hHHiJ hS4LtW, hRepJ, hInNextJ,
        fun a ha => (hFootJ a ha).2,
        fun r hr1 hr2 => ⟨hCellDisj4 r hr1 hr2 (htagLt (by rw [hTagHandle j (le_of_lt hj2)]; decide))
            (by rw [hTagHandle j (le_of_lt hj2)]; omega),
          hCellDisj4 r hr1 hr2 (htagLt (by rw [hTagBranch j (le_of_lt hj2)]; decide))
            (by rw [hTagBranch j (le_of_lt hj2)]; omega),
          hCellDisj4 r hr1 hr2 (htagLt (by rw [hTagMetaG j hj2]; omega))
            (by rw [hTagMetaG j hj2]; omega)⟩,
        Or.inl (lt_of_lt_of_le (lt_trans (Nat.add_lt_add_left hj2 handleBase) hH_end) (Nat.le_add_right heap _)),
        Or.inl (lt_of_lt_of_le (lt_trans (Nat.add_lt_add_left hj2 branchBase) hLevelEnd) (Nat.le_add_right heap _)),
        Or.inl (lt_of_lt_of_le (lt_of_lt_of_le (by omega : levelMeta + d + j < levelMeta + 2 * d) hMetaEnd) (Nat.le_add_right heap _)),
        fun t ht hf => by
          have h1 := (hFootJ _ hf).1
          have : heap + cnt + t < heap1 := by dsimp only [heap1]; omega
          exact absurd (lt_of_lt_of_le this (le_trans hs3_geHeap1 h1)) (Nat.lt_irrefl _), ?_⟩
      by_cases hji1 : j = i0 + 1
      · subst hji1
        have hGPtr4 : s4.mem (levelMeta + d + (i0 + 1)) = s3.regs 6 :=
          (hs4_frame _ (lt_of_lt_of_le (lt_of_lt_of_le (by omega : levelMeta + d + (i0 + 1) < levelMeta + 2 * d) hMetaEnd)
              (le_trans (Nat.le_add_right heap _) hs3_geHeap1))
            (by rcases hSepHL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
            (by rcases hSepBL with h | h <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
            ⟨Or.inr (by dsimp only [levelMeta, d]; omega), Or.inl (by dsimp only [levelMeta, d]; omega)⟩).trans (hMeta3 hj2).2
        refine ⟨?_, by rw [hGPtr4]; exact hHEnd3.trans hs4_lo, ?_⟩
        · rw [hGPtr4]
          exact dynGraphAt_of_agree hH3 (fun a ha1 ha2 =>
            hs4_frame a (lt_of_lt_of_le ha2 hHEnd3)
              (Or.inr (lt_of_lt_of_le hH_end (le_trans (Nat.le_add_right heap _) (le_trans hs2_lo (le_trans h6Lo3 ha1)))))
              (Or.inr (lt_of_lt_of_le hLevelEnd (le_trans (Nat.le_add_right heap _) (le_trans hs2_lo (le_trans h6Lo3 ha1)))))
              ⟨Or.inr (le_trans (by dsimp only [levelMeta, d]; omega) (le_trans hMetaEnd (le_trans (Nat.le_add_right heap _) (le_trans hs2_lo (le_trans h6Lo3 ha1))))),
               Or.inr (le_trans hMetaEnd (le_trans (Nat.le_add_right heap _) (le_trans hs2_lo (le_trans h6Lo3 ha1))))⟩)
        · intro a ha1 ha2
          rw [hGPtr4] at ha1 ha2
          refine ⟨fun r hr1 hr2 => ?_, Or.inr (le_trans (by dsimp only [cnt]; omega) (le_trans hs2_lo (le_trans h6Lo3 ha1)))⟩
          by_cases hri : r = i0
          · subst hri; simp only [↓reduceIte]; exact h6Disj3 a ha1 ha2
          · simp only [hri, ↓reduceIte]
            intro hf; have := (hCores4 r (by omega) hr2).2.2.2.2 a hf
            exact absurd (lt_of_lt_of_le (lt_of_lt_of_le ha2 hHEnd3) this.1) (Nat.lt_irrefl _)
      · obtain ⟨hDGJ, hGLoJ, hGHiJ, _, _, _, hDisjJ, _, _⟩ := hMeta4 j (by omega) hj2
        refine ⟨hDGJ, hGHiJ, fun a ha1 ha2 =>
          ⟨fun r hr1 hr2 => ?_, Or.inr (le_trans (by dsimp only [heap1]; omega) (le_trans hs3_geHeap1 (le_trans hGLoJ ha1)))⟩⟩
        by_cases hri : r = i0
        · subst hri; simp only [↓reduceIte]
          intro hf; exact absurd (lt_of_lt_of_le (hY3FootLt a hf) (le_trans hGLoJ ha1)) (Nat.lt_irrefl _)
        · simp only [hri, ↓reduceIte]
          exact (hDisjJ r (by omega) hr2).2 a ha1 ha2
  have hCoreDisj4All : ∀ j₁ j₂, i0 ≤ j₁ → j₁ < d → i0 ≤ j₂ → j₂ < d → j₁ ≠ j₂ →
      ∀ a, Rcore.foot (coreHandle4 j₁) (coreTok4' j₁) a →
        ¬ Rcore.foot (coreHandle4 j₂) (coreTok4' j₂) a := by
    intro j₁ j₂ h1 h2 h3 h4 hne a ha1 ha2
    by_cases e1 : j₁ = i0 <;> by_cases e2 : j₂ = i0
    · exact hne (e1.trans e2.symm)
    · subst e1; simp only [coreHandle4, coreTok4', ↓reduceIte, e2] at ha1 ha2
      exact absurd (lt_of_lt_of_le (hY3FootLt a ha1) ((hCores4 j₂ (by omega) h4).2.2.2.2 a ha2).1) (Nat.lt_irrefl _)
    · subst e2; simp only [coreHandle4, coreTok4', ↓reduceIte, e1] at ha1 ha2
      exact absurd (lt_of_lt_of_le (hY3FootLt a ha2) ((hCores4 j₁ (by omega) h2).2.2.2.2 a ha1).1) (Nat.lt_irrefl _)
    · simp only [coreHandle4, coreTok4', e1, e2, ↓reduceIte] at ha1 ha2
      exact hCoreDisj4 j₁ j₂ (by omega) h2 (by omega) h4 hne a ha1 ha2
  rw [hChain'] at hLastSubNew
  have hS4Room : s4.regs 4 + 5 * (d - i0) < 2 ^ w := by
    clear r03 hH3 hLen3 hOldForestsSafe2 hCores4 hCoreDisj4 hMeta4 hTermRep4 hTermFoot4 hTermDisj4
      hCores4All hCoreDisj4All hc03
    dsimp only [d, i0] at hSpaceTot hs4_heapLe ⊢; omega
  have hNewTermEndLt : newTermTok ≤ s4.regs 4 := by
    have h1 := hNewTermRep.1
    exact Nat.succ_le_of_lt (hTermFootGe3 (newTermTok - 1) (by omega) (by omega)).2 |> fun h => by omega
  obtain ⟨s5, c4a, coreTok5, r4a, hs5_lo, hs5_hi, hz5, hNewForests5, hCores5_ico, hCoreDisj5_ico,
      hs5_frame, hs5_regs, hc4a⟩ :=
    shiftDeepCollectNewKFBL_runs (w := w) (L := L) (capExp := capExp) (i0 := i0)
      (handleBase := handleBase) (branchBase := branchBase) (levelMeta := levelMeta)
      (newPtrs := heap + cnt) (intCap := tok.intCap) (termHandle := newTermH)
      (vcLast := vCap) (ecLast := eCap) (lsfHdr := newTermLsfHdr)
      (forestPtr := newTermFPtr) (p := p) (ω := ω) (st := s4) next coreHandle4 coreTok4'
      hCoreLocal hiLt h4_71 h4_75 h4_77 h4_78 h4_81 h4_83
      hkW hdW (by omega)
      (le_trans hMetaEnd hHeapLeS4)
      (Nat.succ_le_of_lt (lt_of_lt_of_le hH_end hHeapLeS4))
      (Nat.succ_le_of_lt (lt_of_lt_of_le hLevelEnd hHeapLeS4))
      (le_trans (by dsimp only [heap1, cnt]; omega) (le_trans hs3_geHeap1 hs4_lo))
      hS4Room hz4
      (fun j _ hj2 => hCoreNext j hj2)
      hCores4All hCoreDisj4All rfl hTermB4 rfl rfl hNewTermLSF.2.1
      (le_trans hNewTermBW.2.2.2.2.2.1 hNewTermEndLt)
      (fun e he => hG0Cap e (hLastSubNew he))
      ⟨Or.inl (lt_of_lt_of_le hH_end (Nat.le_add_right heap _)),
        Or.inl (lt_of_lt_of_le hLevelEnd (Nat.le_add_right heap _)),
        Or.inr (le_trans (by dsimp only [heap1]; omega) (le_trans hs3_geHeap1
          (hTermFootGe3 _ (by omega) (by have := hNewTermRep.1; omega)).1)),
        Or.inr (le_trans (by dsimp only [heap1]; omega) (le_trans hs3_geHeap1
          (hTermFootGe3 _ (by have := hNewTermBW.1; have := hNewTermRep.1; omega) (by have := hNewTermBW.2.1; omega)).1)),
        (hTermFootGe3 _ (by omega) (by have := hNewTermRep.1; omega)).2,
        (hTermFootGe3 _ (by have := hNewTermBW.1; have := hNewTermRep.1; omega) (by have := hNewTermBW.2.1; omega)).2,
        fun r hr1 hr2 => by
          have hDisjT (a : ℕ) (ha1 : newTermH ≤ a) (ha2 : a < newTermTok) :
              ¬ Rcore.foot (coreHandle4 r) (coreTok4' r) a := by
            by_cases hri : r = i0
            · subst hri; simp only [coreHandle4, coreTok4', ↓reduceIte]
              intro hf; exact absurd (lt_of_lt_of_le (hY3FootLt a hf) (hTermFootGe3 a ha1 ha2).1) (Nat.lt_irrefl _)
            · simp only [coreHandle4, coreTok4', hri, ↓reduceIte]
              exact hTermDisj4 r (by omega) hr2 a ⟨ha1, ha2⟩
          exact ⟨hCellDisj4 r hr1 hr2 (htagLt (by rw [hTagHandle d le_rfl]; decide)) (by rw [hTagHandle d le_rfl]; omega),
            hCellDisj4 r hr1 hr2 (htagLt (by rw [hTagBranch d le_rfl]; decide)) (by rw [hTagBranch d le_rfl]; omega),
            hDisjT _ (by omega) (by have := hNewTermRep.1; omega),
            hDisjT _ (by have := hNewTermBW.1; have := hNewTermRep.1; omega) (by have := hNewTermBW.2.1; omega)⟩,
        fun a ha1 ha2 => by
          have haIn : newTermH ≤ a ∧ a < newTermTok :=
            ⟨by have := hNewTermBW.2.2.2.2.1; have := hNewTermRep.1; omega,
             by have := hNewTermBW.2.2.2.2.2.1; omega⟩
          refine ⟨fun r hr1 hr2 => ?_,
            Or.inr (le_trans (by dsimp only [heap1]; omega) (le_trans hs3_geHeap1 (hTermFootGe3 a haIn.1 haIn.2).1))⟩
          by_cases hri : r = i0
          · subst hri; simp only [coreHandle4, coreTok4', ↓reduceIte]
            intro hf; exact absurd (lt_of_lt_of_le (hY3FootLt a hf) (hTermFootGe3 a haIn.1 haIn.2).1) (Nat.lt_irrefl _)
          · simp only [coreHandle4, coreTok4', hri, ↓reduceIte]
            exact hTermDisj4 r (by omega) hr2 a haIn⟩
      (fun j hj1 hj2 e he => by
        have hLsfJ := hLsfSub j hj1 hj2
        rw [hChain'] at hLsfJ
        exact hG0Cap e (hLsfJ.2 he))
  -- Compose `r03` and `r4a`
  have rAll : Runs w p ω
      (shiftDeepInitRegsKFBL ;; shiftDeepCollectOldKFBL (opCore 2) ;;
        shiftDeepRestartAndReadoutKFBL (opCore 1) (opCore 3) (opCore 2) coreLenProc (opCore 5) ;;
        ordRebuildSuffixProgramKFBLStore initCore (opCore 3) (opCore 2) coreLenProc (opCore 5)
          lastInit ;;
        (.assign 20 (.reg 71) ;; collectLSFForestsLoop (opCore 2) 81 ;; collectTermForestStmt 81))
      (startState [root, i0, heap] mem pos) .normal s5 (c03 + c4a + 1) := by
    rcases runs_seq_iff.mp r03 with ⟨_, _, _, hne, _⟩ | ⟨s1', ca, cbcd, ra, rbcd, hcEq⟩
    · exact absurd hne (by simp)
    · rcases runs_seq_iff.mp rbcd with ⟨_, _, _, hne2, _⟩ | ⟨s2', cb, ccd, rb, rcd, hcEq2⟩
      · exact absurd hne2 (by simp)
      · rcases runs_seq_iff.mp rcd with ⟨_, _, _, hne3, _⟩ | ⟨s3', cc, cd, rc, rd, hcEq3⟩
        · exact absurd hne3 (by simp)
        · exact runs_seq_iff.mpr (Or.inr ⟨s1', ca, cb + (cc + (cd + c4a + 1) + 1) + 1, ra,
            runs_seq_iff.mpr (Or.inr ⟨s2', cb, cc + (cd + c4a + 1) + 1, rb,
              runs_seq_iff.mpr (Or.inr ⟨s3', cc, cd + c4a + 1, rc,
                runs_seq_iff.mpr (Or.inr ⟨s4, cd, c4a, rd, r4a, rfl⟩), rfl⟩), rfl⟩),
            by omega⟩)
  have hPhi4Split :
      (Finset.Ico i0 d).sum (fun j => Rcore.phi (coreHandle4 j) (coreTok4' j) s4.mem) =
      Rcore.phi (tok.coreHandle i0) yI0_3 s3.mem +
      (Finset.Ico (i0 + 1) d).sum (fun j => Rcore.phi (s4.mem (handleBase + j)) (coreTok4 j) s4.mem) := by
    have hIns : Finset.Ico i0 d = insert i0 (Finset.Ico (i0 + 1) d) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hIns, Finset.sum_insert (by simp)]
    congr 1
    · simp only [coreHandle4, coreTok4', ↓reduceIte]; exact hY3Phi4
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      obtain ⟨hj1, _⟩ := Finset.mem_Ico.mp hj
      simp only [coreHandle4, coreTok4', show j ≠ i0 by omega, ↓reduceIte]
  have hCostTot := hOps.costTotal model i hiLt hBranLt (hScIn0 i0 le_rfl hiLt) hModelK
  dsimp only at hCostTot
  have hDSub1 : (d - i0) * (Psc.readout + 48) ≤ d * (Psc.readout + 48) :=
    Nat.mul_le_mul_right _ (Nat.sub_le d i0)
  have hS5Space : s5.regs 4 + 3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L) ≤ heap + deepSpace := by
    clear rAll r4a r03 hH3 hLen3 hOldForestsSafe2 hCores4 hCoreDisj4 hMeta4 hTermRep4 hTermFoot4
      hTermDisj4 hCores4All hCoreDisj4All hCores5_ico hCoreDisj5_ico hNewForests5 hc03 hc4a hCostTot
    dsimp only [d, i0] at hSpaceTot hs4_heapLe hs5_hi ⊢; omega
  have hCostEnd :
      (c03 + c4a + 1) + (Finset.Ico i0 d).sum (fun j => Rcore.phi (coreHandle4 j) (coreTok5 j) s5.mem) +
        85 * (graphListEdgeSum (chainSuffixForests model.chain i0) +
          graphListEdgeSum (chainSuffixForests next i0)) + 210 * (d + 1) + 400 ≤
      deepFixed + toolMul * (next.totalRuntime - model.chain.totalRuntime) +
        (Finset.Ico i0 d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0) := by
    have h2d : 2 * cfg.P.d * (Psc.readout + 48) = 2 * (cfg.P.d * (Psc.readout + 48)) := Nat.mul_assoc 2 _ _
    rw [hPhi4Split] at hc4a
    clear rAll r4a r03 hH3 hLen3 hOldForestsSafe2 hCores4 hCoreDisj4 hMeta4 hTermRep4 hTermFoot4
      hTermDisj4 hCores4All hCoreDisj4All hCores5_ico hCoreDisj5_ico hNewForests5 hPhi4Split
    dsimp only [d, i0, chain, next, handleBase] at hc03 hc4a hCostTot hDSub1 ⊢
    omega
  refine ⟨s2, s3, s4, s5, c03 + c4a + 1, newTermTok, yI0_2, yI0_3,
    coreTok4, coreTok5, rAll, hs2_lo, h4Lo3, hs4_lo, hs5_lo, hS5Space, hz5, hOldForestsSafe2,
    hFootI0_2, hs2_frame, hBr3, hFootI0_3, hH3, hLen3, h6Lo3, hHEnd3, h6Disj3, h7Lo3, hLenEnd3,
    h7Disj3, h6Le7_3, hMeta3, hs3_frame, hCores4, hMeta4, hMetaOrd4, hTermB4, hTermRep4, hTermFoot4, hTermDisj4,
    hs4_frame, hNewForests5,
    fun j hj1 hj2 => ⟨(hCores4All j hj1 hj2).1, (hCores4All j hj1 hj2).2.1,
      (hCores5_ico j hj1 hj2).1, (hCores5_ico j hj1 hj2).2⟩,
    hCoreDisj5_ico, hs5_frame,
    (hs5_regs 70 (by decide)).trans h4_70,
    (hs5_regs 71 (by decide)).trans h4_71,
    (hs5_regs 73 (by decide)).trans h4_73,
    (hs5_regs 75 (by decide)).trans h4_75,
    (hs5_regs 79 (by decide)).trans h4_79,
    (hs5_regs 80 (by decide)).trans h4_80,
    (hs5_regs 81 (by decide)).trans h4_81,
    hCostEnd⟩

end MinCostFlow.MinRatio
