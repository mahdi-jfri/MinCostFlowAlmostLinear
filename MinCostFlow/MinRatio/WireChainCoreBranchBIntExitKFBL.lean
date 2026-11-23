module

public import MinCostFlow.MinRatio.WireChainCoreBranchBIntOutKFBL
import WordRAM.Tactic

/-!
# The interior step of Branch B from the loop exit under `KFBL` (`WireChainCoreBranchBIntExitKFBL`)

This file composes the three run lemmas of the interior step `wireBranchBIntKFBL` (defined in
`WireChainCoreBranchBIntOutKFBL`) from the exit of the Branch B loop at a level `0 < i₀ < d`
whose counter passed its threshold. The result, `wireBranchBIntKFBL_runs_exit`, gives the facts
`BranchBIntOutKFBL` at the end state:
* every core sits at the handle `mem (handleBase + j)`, the old handle below `i₀` and a new one
  from `i₀` on;
* the slots of the levels below `i₀` are finished (the slot of level `i₀ - 1` gets its descriptor
  again by `BranchBDoneSlots.refresh`, since op `5` ran on that core);
* the cells, graphs and lengths of all levels and the new last level are those of the rebuilt
  chain;
* the old and new forest lists for the tree sync, and a frame below the select base.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

set_option maxHeartbeats 1600000 in
/-- **The interior step of Branch B, from the exit of the loop.** The loop exits at
`0 < i₀ < d` with the invariant `I` at the state `sE`, and the counter of level `i₀` passed its
threshold (`hFire`), so the model invariant `hM` at the exit gives the rebuild facts of level
`i₀`. The run starts at `st`, which differs from `sE` only in `regs 16, 17, 18, 99`. The old
last forest is at `mem (oldPtrs + d)`, inside the footprint of the old last level (`hOldLast`):
the assembly stores it there before the loop. The space, cost and cap premises of the suffix
rebuild are those of `wireBranchBIntRebNewKFBL_runs`. The cost is the sum of the costs of the
three parts, against the potentials of the cores before and after. -/
theorem wireBranchBIntKFBL_runs_exit
    {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy N0 oldPtrs newPtrs intCap i₀ wordExp stretchPrec
      capLimit coreLenProc lastInit lastMul lastSpace : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {opCore opLast : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ}
    {ℓ' g' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ}
    {ch : ChainState cfg.T cfg.P} {curG : MGraph} {curU : List Update}
    {curEditsList : List OrdEdit} {curEnc : ℕ} {oldOrd : ℕ → List End} {sE st : State}
    {tok : ℕ → Rcore.τ} {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists} {levelSpace levelCost : ℕ → ℕ}
    (E : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore
      p opCore)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hOldLo : A.selBase + 1 + 12 * cfg.P.d ≤ oldPtrs)
    (hOldNew : oldPtrs + (cfg.P.d + 1) ≤ newPtrs)
    (hNewHi : newPtrs + (cfg.P.d + 1) ≤ A.heapFloor)
    (hN0 : N0 = cfg.N₀) (hLvlM : ∀ j < cfg.P.d, ch0.lvlM j = levelM cfg.TP cfg.P j)
    (hN00 : ch0.N₀ = N0) (hPos : 0 < i₀) (hLt : i₀ < cfg.P.d)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
      EWc ULc ch0 termTok i₀ ch curG curU curEditsList oldOrd sE tok curBatch curBatchWords
      curEdits curEditsWords levelU levelUS D)
    (hM : UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen
      ℓ' g' (cfg.P.d - i₀) i₀ ch curG curU curEnc oldOrd)
    (hFire : intRebuildThreshold cfg.P N0 i₀ < ch.updCount i₀ + curU.length)
    (hstMem : st.mem = sE.mem)
    (hstRegs : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 99 → st.regs r = sE.regs r)
    (h71 : sE.regs 71 = 0) (h80 : sE.regs 80 = oldPtrs) (h81 : sE.regs 81 = newPtrs)
    (hIn0 : ∀ j, i₀ ≤ j → j < cfg.P.d →
      SparseCoreOrdInput cfg.T cfg.P.k (ch0.lvlM j) ch0.N₀ (ch0.scState j) (ch0.G j)
        (ch0.levelOrd j) (ch0.updCount j))
    (hOldLast : ∃ vc ec, DynGraphAt sE.mem (sE.mem (oldPtrs + cfg.P.d)) vc ec
        (ch0.lastLSFs ch0.lastBran).F.F ∧
      ∀ a, sE.mem (oldPtrs + cfg.P.d) ≤ a →
        a < sE.mem (oldPtrs + cfg.P.d) + dynGraphSize vc ec → RL.foot (A.coreH cfg.P.d) termTok a)
    (hOldFCap : ∀ j, i₀ ≤ j → j < cfg.P.d →
      ∀ e ∈ (cfg.T.lsfs (ch0.scState j) (ch0.bran j)).F.F.E, e < intCap)
    (hOldLastFCap : ∀ e ∈ (ch0.lastLSFs ch0.lastBran).F.F.E, e < intCap)
    (next : ChainState cfg.T cfg.P)
    (hNext : next = (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
      { ch with ℓ := ℓ', g := g' } i₀ curG curEnc).1)
    (hWordExpEq : Psc.wordExp = wordExp) (hInitOrdEq : ToolInitOrdEqOnE cfg.T)
    (hNextN : ∀ j ≤ cfg.P.d, (next.G j).n ≤ next.N₀)
    (hNextRot : ∀ j < cfg.P.d, ordRotWords (chainLevelOrdAbs next j) (next.bran j) ≤
      1 + 2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m)
    (hImpl : ∀ j, i₀ ≤ j → j < cfg.P.d →
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth cfg.T (next.G j) cfg.P.k (next.lvlM j)
          next.N₀ vCap eCap capExp Psc alloc) ∧
      SparseCoreReadoutFootAt fmt L depth cfg.T (next.G j) cfg.P.k (next.lvlM j) next.N₀ vCap
        eCap capExp Psc alloc Rcore p opCore)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hLastImpl :
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
        (next.G cfg.P.d).E).Implements w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L (next.G cfg.P.d) vCap eCap lastMul
          stretchPrec lastAlloc))
    (hLevelSpaceDom : ∀ j gB lB grB oB h, i₀ ≤ j → j < cfg.P.d →
      ordLevelSpace L capExp capLimit
        (alloc 6 [gB, lB, grB, oB, cfg.P.k, next.lvlM j, next.N₀, L, fmt.precision, depth, h])
        (next.lvlM j) next.N₀ (next.G (j + 1)).m ≤ levelSpace j)
    (hLevelCostDom : ∀ j, i₀ ≤ j → j < cfg.P.d →
      updateCoreRebuildLevelCost L capExp cfg Psc next j ≤ levelCost j)
    (hLastSpaceDom : ∀ gB lB h, lastAlloc 1 [gB, lB, L, fmt.precision, h] ≤ lastSpace)
    (hFCap : ∀ j, i₀ ≤ j → j < cfg.P.d →
      ∀ e ∈ (cfg.T.lsfs (next.scState j) (next.bran j)).F.F.E, e < intCap)
    (hLastFCap : ∀ e ∈ (next.lastLSFs next.lastBran).F.F.E, e < intCap)
    (hLWord : L < 2 ^ w) (hPWord : P < 2 ^ w) (hWidth : P ≤ 4 * L) (hDepthW : depth < 2 ^ w)
    (hNW : N0 < 2 ^ w)
    (hRoom : sE.regs 4 + 10 * (cfg.P.d - i₀) +
      (1 + ordRotWords (chainLevelOrdAbs ch (i₀ - 1)) (ch.bran (i₀ - 1))) +
      (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace + 7 < 2 ^ w) :
    ∃ (out : State) (cost termTokN : ℕ) (tokN : ℕ → Rcore.τ),
      Runs w p ω (wireBranchBIntKFBL dgApply initCore (opCore 3) (opCore 2) coreLenProc
        (opCore 5) lastInit) st .normal out cost ∧
      out.regs 4 ≤ sE.regs 4 + 10 * (cfg.P.d - i₀) +
        (1 + ordRotWords (chainLevelOrdAbs ch (i₀ - 1)) (ch.bran (i₀ - 1))) +
        (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace + 7 ∧
      BranchBIntOutKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
        (capExp := capExp) A oldPtrs newPtrs intCap i₀ ch0 ch next levelU D sE out tok tokN
        termTokN ∧
      cost + (Finset.range cfg.P.d).sum
          (fun j => Rcore.phi (out.mem (A.handleBase + j)) (tokN j) out.mem) ≤
        2 * ((cfg.P.d - i₀) * (Psc.readout + 48)) + 670 * curBatchWords +
          Psc.mul * (ordRotWords (chainLevelOrdAbs ch (i₀ - 1)) (ch.bran (i₀ - 1)) + 1) *
            SparseCore.bundleLogFactor (levelM cfg.TP cfg.P (i₀ - 1)) cfg.N₀ +
          (Finset.Ico i₀ cfg.P.d).sum (fun j => levelCost j + 9) +
          lastMul * (cfg.L.cost (next.G cfg.P.d) + 1) + Psc.readout + 15 * (cfg.P.d - i₀) +
          413 + branchBPhiSum Rcore A tok sE.mem := by
  -- the model facts at the exit
  obtain ⟨hFloor, _, _, _, _, hr72, _, _, hr75, _, hr77, hr78, _, hr83, hr85, _, _, _, hr96,
    _, _, _⟩ := I.regs
  have hN : ch.N₀ = N0 := I.modelFrame.2.2.2.2.2.1
  have hLvlCh : ∀ j < cfg.P.d, ch.lvlM j = levelM cfg.TP cfg.P j := fun j hj => by
    rw [I.modelFrame.2.2.2.2.2.2.1]; exact hLvlM j hj
  obtain ⟨rem, hrem⟩ : ∃ rem, cfg.P.d - i₀ = rem + 1 := ⟨cfg.P.d - i₀ - 1, by omega⟩
  rw [hrem] at hM
  obtain ⟨_, hValid, hCaps, hCurG, _, hIf⟩ := hM
  have hFire' : intRebuildThreshold cfg.P ch.N₀ i₀ < ch.updCount i₀ + curU.length := by
    rw [hN]; exact hFire
  simp only [hFire', ↓reduceIte] at hIf
  obtain ⟨hReb, hInPrev0⟩ := hIf
  have hi0 : i₀ ≠ 0 := by omega
  rw [rebuildStartGraph_pos hi0, rebuildStartFn_pos hi0, rebuildStartFn_pos hi0] at hReb
  have hInPrev := hInPrev0 hPos
  clear hi0 hrem hInPrev0
  -- the two subtractions as linear facts, so that `omega` needs no case split on them
  have hsub1 : i₀ - 1 + 1 = i₀ := by omega
  have hsub2 : cfg.P.d - i₀ + i₀ = cfg.P.d := by omega
  obtain ⟨hPre, hNG, _, _, _, hRCN, hRebW, hAbsPre, _, hLenPre, hLenI, hModelLevel, _⟩ :=
    branchBIntNext_facts (fmt := fmt) (Psc := Psc) ch curG ℓ' g' curEnc i₀ next hNext hPos hLt
      hReb hWordExpEq E.prec hInitOrdEq hNextN hNextRot
  -- the layout bounds; the separations of the arrays are used only through the lemmas on
  -- `BranchBIntKeepCell`, so that no `omega` call below splits on them
  have hHBLt := S.hbLt
  have hBBLt := S.bbLt
  have hMetaLt := S.metaLt
  have hUCLt := S.ucLt
  have hRCLt := S.rcLt
  have hGLt : A.gPtr0 i₀ + dynGraphSize vCap eCap ≤ A.selBase := S.gLt i₀ hLt
  have hm1 : i₀ - 1 < cfg.P.d := by omega
  have hGLt1 : A.gPtr0 (i₀ - 1) + dynGraphSize vCap eCap ≤ A.selBase := S.gLt (i₀ - 1) hm1
  have hSlotLe : A.selBase + 1 + 12 * cfg.P.d ≤ A.heapFloor := by omega
  have hFootLoc := I.footLoc
  have hFootOld := I.footOld
  obtain ⟨s, c1, tokM, ordPtr, ordWords, r1, h1hi, M, hc1⟩ :=
    wireBranchBIntOldKFBL_runs (ω := ω) (st := st) E S hOldLo (by omega) hN0 hLvlM hN00 hPos
      hLt I hstMem hstRegs h71 h80 hIn0 hValid hCaps hCurG hRebW hInPrev (by omega)
  obtain ⟨s3, c2, termTokN, coreTok, r2, h3hi, B, hc2⟩ :=
    wireBranchBIntRebNewKFBL_runs (ω := ω) E S hOldLo (by omega) (by omega) hNewHi hPos hLt I M
      h71 h81 next hNext hReb hWordExpEq hInitOrdEq hNextN hNextRot hImpl hcapLim hCoreLenProc
      hLastImpl hLevelSpaceDom hLevelCostDom hLastSpaceDom hFCap hLastFCap hLWord hPWord hWidth
      hDepthW hNW (by omega)
  have hsE4 : sE.regs 4 < s.regs 4 := by have := M.heapLo; have := M.ord.2.2.1; omega
  have hs3 : s.regs 4 ≤ s3.regs 4 := B.heapLo
  have hRoom3 : s3.regs 4 + 7 < 2 ^ w := by omega
  have hHeap3 : s3.regs 4 + 7 ≤ sE.regs 4 + 10 * (cfg.P.d - i₀) +
      (1 + ordRotWords (chainLevelOrdAbs ch (i₀ - 1)) (ch.bran (i₀ - 1))) +
      (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace + 7 := by omega
  clear hRoom h1hi h3hi
  have hR3 (r : ℕ) (h70 : 70 ≤ r) (h99 : r ≠ 99) : s3.regs r = sE.regs r :=
    (B.regs r h70).trans (M.regs r h70 h99)
  have hTokM1 : ∀ a, Rcore.foot (A.coreH (i₀ - 1)) (tokM (i₀ - 1)) a →
      Rcore.foot (A.coreH (i₀ - 1)) (tok (i₀ - 1)) a ∨ (sE.regs 4 ≤ a ∧ a < s.regs 4) :=
    (M.reps (i₀ - 1) hm1).2
  -- the words below `sE.regs 4` that the first two parts keep
  have hKeep3 : ∀ a < sE.regs 4,
      (∀ j, i₀ ≤ j + 1 → j < cfg.P.d → ¬ Rcore.foot (A.coreH j) (tok j) a) →
      (a < A.gPtr0 i₀ ∨ A.gPtr0 i₀ + dynGraphSize vCap eCap ≤ a) →
      BranchBIntKeepCell cfg.P.d i₀ A a →
      (a < oldPtrs + i₀ ∨ oldPtrs + cfg.P.d ≤ a) →
      (a < newPtrs + i₀ ∨ newPtrs + (cfg.P.d + 1) ≤ a) → s3.mem a = sE.mem a :=
    fun a ha hc hg hk ho hn =>
      (B.frame a (by omega) hk.2.1 hk.2.2.1 hk.2.2.2 hn).trans (M.frame a ha hc hg hk.1 ho)
  have hK3S : ∀ x, BranchBStaticWord cfg.P.d A x → BranchBIntKeepCell cfg.P.d i₀ A x →
      s3.mem x = sE.mem x := fun x hx hk => by
    obtain ⟨hxs, hxf, hxg, _⟩ := branchBStaticWord_off S I.static hx
    exact hKeep3 x (by omega) (fun j _ hj => hxf j hj) (hxg i₀ hLt).1 hk (Or.inl (by omega))
      (Or.inl (by omega))
  -- the cells of the levels below `i₀` and the other rebuild counters stay
  have h3HB : ∀ j < i₀, s3.mem (A.handleBase + j) = sE.mem (A.handleBase + j) := fun j hj =>
    hK3S _ (.hb (by omega) (by omega)) (.hb S hj hLt)
  have h3BB : ∀ j < i₀, s3.mem (A.branchBase + j) = sE.mem (A.branchBase + j) := fun j hj =>
    hK3S _ (.bb (by omega) (by omega)) (.bb S hj hLt)
  have h3LM : ∀ j ≤ i₀, s3.mem (A.levelMeta + j) = sE.mem (A.levelMeta + j) := fun j hj =>
    hK3S _ (.lm (by omega) (by omega)) (.lm S hj hLt)
  have h3LMd : ∀ j ≤ i₀, s3.mem (A.levelMeta + cfg.P.d + j) =
      sE.mem (A.levelMeta + cfg.P.d + j) := fun j hj =>
    hK3S _ (.lm (by omega) (by omega)) (.lmd S hj hLt)
  have h3RC : ∀ j < cfg.P.d, j ≠ i₀ → s3.mem (A.rcBase + j) = sE.mem (A.rcBase + j) :=
    fun j hj hne => hK3S _ (.rc (by omega) (by omega)) (.rc S hj hne)
  have h3RCi : s3.mem (A.rcBase + i₀) = s.mem (A.rcBase + i₀) := by
    obtain ⟨k1, k2, k3⟩ := branchBInt_rc_frame S hLt
    exact B.frame _ (by omega) k1 k2 k3 (Or.inl (by omega))
  have h3UC : ∀ j < i₀, s3.mem (A.ucBase + j) = sE.mem (A.ucBase + j) := fun j hj => by
    refine hKeep3 _ (by omega) (fun r _ hr => ((I.static r hr).2.2.2.1 j (by omega)).2.2.2.1)
      ?_ (.uc S (by omega) hLt) (Or.inl (by omega)) (Or.inl (by omega))
    by_contra hc
    simp only [not_or, not_lt, not_le] at hc
    obtain ⟨_, _, _, _, _, _, _, g8, _⟩ := S.gSep i₀ hLt _ hc.1 hc.2
    rcases g8 with g8 | g8 <;> omega
  -- the core of level `i₀ - 1` at the start of the tail
  have hLoc1 := E.loc (A.coreH (i₀ - 1)) (chainLevelOrdAbs ch (i₀ - 1)) (tokM (i₀ - 1)) s.mem
    s3.mem (fun a ha => by
      rcases hTokM1 a ha with h0 | ⟨_, h2⟩
      · have hlt := (I.reps (i₀ - 1) hm1).2 a h0
        obtain ⟨f1, f2, f3, _, f5, _⟩ := branchBCoresDisjStatic_footSep I.static hm1 h0
        have hk : BranchBIntKeepCell cfg.P.d i₀ A a := .of_sep f1 f2 f3 f5 hLt
        refine (B.frame a (by omega) hk.2.1 hk.2.2.1 hk.2.2.2 ?_).symm
        rcases hFootLoc (i₀ - 1) hm1 a h0 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      · exact (B.frame a h2 (Or.inr (by omega)) (Or.inr (by omega))
          ⟨Or.inr (by omega), Or.inr (by omega)⟩ (Or.inr (by omega))).symm)
  have hRep1 : Rcore.rep (A.coreH (i₀ - 1)) (chainLevelOrdAbs ch (i₀ - 1)) (tokM (i₀ - 1))
      s3.mem := by
    have h := (M.reps (i₀ - 1) hm1).1
    simp only [show ¬ i₀ ≤ i₀ - 1 by omega, ↓reduceIte] at h
    exact hLoc1.1 h
  obtain ⟨_, _, c3t, c4t, c5t, c6t, c7t, _, _, _⟩ := I.cells (i₀ - 1) hm1
  have hG1 : DynGraphAt s3.mem (A.gPtr0 (i₀ - 1)) vCap eCap (ch.G (i₀ - 1)) :=
    dynGraphAt_of_agree (I.graphs (i₀ - 1) hm1) (fun x hx1 hx2 => by
      obtain ⟨_, _, g3, g4, _, g6, g7, _, g9⟩ := S.gSep (i₀ - 1) hm1 x hx1 hx2
      exact hKeep3 x (by omega)
        (fun j _ hj => (I.static j hj).2.2.2.2.1 (i₀ - 1) hm1 x hx1 hx2)
        ((g9 i₀ hLt).2 (by omega)) (.of_sep g3 g4 g6 (g7.imp_right Nat.le_of_lt) hLt)
        (Or.inl (by omega)) (Or.inl (by omega)))
  have hInT : SparseCoreOrdInput cfg.T cfg.P.k (levelM cfg.TP cfg.P (i₀ - 1)) cfg.N₀
      (ch.scState (i₀ - 1)) (ch.G (i₀ - 1)) (ch.levelOrd (i₀ - 1)) (ch.updCount (i₀ - 1)) := by
    rw [← hLvlCh (i₀ - 1) hm1, ← hN0, ← hN]; exact hInPrev
  -- Part 3
  obtain ⟨out, c3, ret, y, r3, hretlo, hrethi, hout4, hout97, hregsT, hRepY, hFootY, hzOut,
      hSel, hUC0, hFrT, h8, h9, hSV, hT0, hT1, hc3⟩ :=
    wireBranchBIntTailKFBL_runs (tool := cfg.T) (ω := ω) (st := s3) (d := cfg.P.d) (idx := i₀)
      (selBase := A.selBase) (ucBase := A.ucBase) (cur := s3.regs 4)
      (handleBase := A.handleBase) (branchBase := A.branchBase) (levelMeta := A.levelMeta)
      (handle := A.coreH (i₀ - 1)) (branch := ch.bran (i₀ - 1)) (graph := A.gPtr0 (i₀ - 1))
      (a := ⟨ch.scState (i₀ - 1), ch.G (i₀ - 1), ch.levelOrd (i₀ - 1), ch.updCount (i₀ - 1)⟩)
      (x := tokM (i₀ - 1)) E.loc (E.footAt (i₀ - 1) hm1)
      ⟨rfl, (hR3 72 (by omega) (by omega)).trans hr72,
        (hR3 75 (by omega) (by omega)).trans hr75, (hR3 77 (by omega) (by omega)).trans hr77,
        (hR3 78 (by omega) (by omega)).trans hr78, (hR3 83 (by omega) (by omega)).trans hr83,
        (hR3 85 (by omega) (by omega)).trans hr85, (hR3 96 (by omega) (by omega)).trans hr96⟩
      hLt.le (by omega)
      ⟨(h3HB (i₀ - 1) (by omega)).trans c3t, (h3BB (i₀ - 1) (by omega)).trans c4t,
        (h3LMd (i₀ - 1) (by omega)).trans c7t⟩
      ⟨by omega, by omega, by omega⟩ c5t E.kW c6t hG1 (by omega) hRep1 hInT
      (fun z hz => by
        rcases hTokM1 z hz with h | h
        · have := (I.reps (i₀ - 1) hm1).2 z h; omega
        · omega)
      B.zero (by omega) (by omega)
      ⟨fun hf => by
        rcases hTokM1 _ hf with h | h
        · rcases hFootLoc (i₀ - 1) hm1 _ h with h' | h' <;> omega
        · omega,
       fun hf => by
        rcases hTokM1 _ hf with h | h
        · rcases hFootLoc (i₀ - 1) hm1 _ h with h' | h' <;> omega
        · omega⟩
      (fun z hz => by
        rcases hz with ⟨hz1, hz2⟩ | hz
        · obtain ⟨n1, n2, n3⟩ := branchBStatic_uc_ne S (z := z) (by omega) hz2 hm1
          refine ⟨by omega, fun hf => ?_, ?_, n1, n2, n3, by omega, by omega⟩
          · rcases hTokM1 z hf with h | h
            · obtain ⟨_, _, _, f4, _, _⟩ := branchBCoresDisjStatic_footSep I.static hm1 h
              rcases f4 with f4 | f4 <;> omega
            · omega
          · by_contra hc
            simp only [not_or, not_lt, not_le] at hc
            obtain ⟨_, _, _, _, _, _, _, g8, _⟩ := S.gSep (i₀ - 1) hm1 z hc.1 hc.2
            rcases g8 with g8 | g8 <;> omega
        · subst hz
          refine ⟨by omega, fun hf => ?_, Or.inr (by omega), by omega, by omega, by omega,
            by omega, by omega⟩
          rcases hTokM1 _ hf with h | h
          · rcases hFootLoc (i₀ - 1) hm1 _ h with h' | h' <;> omega
          · omega)
      (Or.inr (by omega))
  clear hr72 hr75 hr77 hr78 hr83 hr85 hr96 c3t c4t c5t c6t c7t hInT hInPrev hRoom3 hcapLim
    hLWord hPWord hWidth hDepthW hNW h71 h80 h81 hN0 hN00 hN hLvlCh hFire hFire' hWordExpEq
    hRebW
  -- the words that the tail keeps
  have hKeepHigh : ∀ a, s.regs 4 ≤ a → a < s3.regs 4 → out.mem a = s3.mem a := fun a h1 h2 =>
    hFrT a h2 (fun hf => by
      rcases hTokM1 a hf with h | h
      · have := (I.reps (i₀ - 1) hm1).2 a h; omega
      · omega) (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have hKeepMid : ∀ a, A.selBase + 1 + 12 * cfg.P.d ≤ a → a < A.heapFloor →
      out.mem a = s3.mem a := fun a h1 h2 =>
    hFrT a (by omega) (fun hf => by
      rcases hTokM1 a hf with h | h
      · rcases hFootLoc (i₀ - 1) hm1 a h with h' | h' <;> omega
      · omega) (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have hKeepTS : ∀ x, BranchBStaticWord cfg.P.d A x → out.mem x = s3.mem x := fun x hx => by
    obtain ⟨hxs, hxf, _, hxu⟩ := branchBStaticWord_off S I.static hx
    refine hFrT x (by omega) (fun hf => ?_) ?_ (by omega) (by omega) (by omega)
    · rcases hTokM1 x hf with h | h
      · exact hxf (i₀ - 1) hm1 h
      · omega
    · by_contra hc
      simp only [not_or, not_lt, not_le] at hc
      exact hxu (x - A.ucBase) (by omega) (by omega)
  -- the words below `sE.regs 4` that the whole step keeps
  have hKeepAll : ∀ a < sE.regs 4,
      (∀ j, i₀ ≤ j + 1 → j < cfg.P.d → ¬ Rcore.foot (A.coreH j) (tok j) a) →
      (a < A.gPtr0 i₀ ∨ A.gPtr0 i₀ + dynGraphSize vCap eCap ≤ a) →
      BranchBIntKeepCell cfg.P.d i₀ A a →
      (a < A.ucBase + i₀ ∨ A.ucBase + cfg.P.d ≤ a) →
      (a < A.selBase ∨ (A.selBase < a ∧ a < A.selBase + 1 + 12 * cfg.P.d ∧
        a ≠ A.selBase + 1 + 12 * (i₀ - 1) + 8 ∧ a ≠ A.selBase + 1 + 12 * (i₀ - 1) + 9) ∨
        A.heapFloor ≤ a) →
      out.mem a = sE.mem a := fun a ha hc hg hk hu hmid => by
    have hnf : ¬ Rcore.foot (A.coreH (i₀ - 1)) (tokM (i₀ - 1)) a := fun hf => by
      rcases hTokM1 a hf with h | h
      · exact hc (i₀ - 1) (by omega) hm1 h
      · omega
    rcases hmid with hm | ⟨_, hm2, hm3, hm4⟩ | hm
    · rw [← hKeep3 a ha hc hg hk (Or.inl (by omega)) (Or.inl (by omega))]
      exact hFrT a (by omega) hnf hu (by omega) (by omega) (by omega)
    · rw [← hKeep3 a ha hc hg hk (Or.inl (by omega)) (Or.inl (by omega))]
      exact hFrT a (by omega) hnf hu (by omega) hm3 hm4
    · rw [← hKeep3 a ha hc hg hk (Or.inr (by omega)) (Or.inr (by omega))]
      exact hFrT a (by omega) hnf hu (by omega) (by omega) (by omega)
  -- the footprints of the cores below `i₀ - 1`
  have hLowLoc : ∀ j < i₀ - 1, ∀ a, Rcore.foot (A.coreH j) (tok j) a → out.mem a = s.mem a := by
    intro j hj a ha
    have hlt := (I.reps j (by omega)).2 a ha
    obtain ⟨f1, f2, f3, f4, f5, _⟩ :=
      branchBCoresDisjStatic_footSep I.static (r := j) (by omega) ha
    have hk : BranchBIntKeepCell cfg.P.d i₀ A a := .of_sep f1 f2 f3 f5 hLt
    have hnf : ¬ Rcore.foot (A.coreH (i₀ - 1)) (tokM (i₀ - 1)) a := fun hf => by
      rcases hTokM1 a hf with h | h
      · exact I.disj j (by omega) (i₀ - 1) hm1 (by omega) a ha h
      · omega
    rcases hFootLoc j (by omega) a ha with f7 | f7
    · exact (hFrT a (by omega) hnf (f4.imp_left (fun h => by omega)) (by omega) (by omega)
        (by omega)).trans (B.frame a (by omega) hk.2.1 hk.2.2.1 hk.2.2.2 (Or.inl (by omega)))
    · exact (hFrT a (by omega) hnf (Or.inr (by omega)) (by omega) (by omega)
        (by omega)).trans (B.frame a (by omega) hk.2.1 hk.2.2.1 hk.2.2.2 (Or.inr (by omega)))
  -- the cells at the end
  have hOHB : ∀ j < i₀, out.mem (A.handleBase + j) = sE.mem (A.handleBase + j) := fun j hj =>
    (hKeepTS (A.handleBase + j) (.hb (by omega) (by omega))).trans (h3HB j hj)
  have hOBB : ∀ j < i₀, out.mem (A.branchBase + j) = sE.mem (A.branchBase + j) := fun j hj =>
    (hKeepTS (A.branchBase + j) (.bb (by omega) (by omega))).trans (h3BB j hj)
  have hOLM : ∀ j ≤ i₀, out.mem (A.levelMeta + j) = sE.mem (A.levelMeta + j) := fun j hj =>
    (hKeepTS (A.levelMeta + j) (.lm (by omega) (by omega))).trans (h3LM j hj)
  have hOLMd : ∀ j ≤ i₀, out.mem (A.levelMeta + cfg.P.d + j) =
      sE.mem (A.levelMeta + cfg.P.d + j) := fun j hj =>
    (hKeepTS (A.levelMeta + cfg.P.d + j) (.lm (by omega) (by omega))).trans (h3LMd j hj)
  have hORC : ∀ j < cfg.P.d, j ≠ i₀ → out.mem (A.rcBase + j) = sE.mem (A.rcBase + j) :=
    fun j hj hne => (hKeepTS (A.rcBase + j) (.rc (by omega) (by omega))).trans (h3RC j hj hne)
  have hOUC : ∀ j < i₀, out.mem (A.ucBase + j) = sE.mem (A.ucBase + j) := fun j hj => by
    have hnf : ¬ Rcore.foot (A.coreH (i₀ - 1)) (tokM (i₀ - 1)) (A.ucBase + j) := fun hf => by
      rcases hTokM1 _ hf with h0 | h0
      · exact ((I.static (i₀ - 1) hm1).2.2.2.1 j (by omega)).2.2.2.1 h0
      · omega
    rw [hFrT (A.ucBase + j) (by omega) hnf (Or.inl (by omega)) (by omega) (by omega)
      (by omega)]
    exact h3UC j hj
  -- the new tokens
  obtain ⟨tokN, htokN⟩ : ∃ f : ℕ → Rcore.τ,
      f = fun j => if j = i₀ - 1 then y else if i₀ ≤ j then coreTok j else tok j := ⟨_, rfl⟩
  have htN1 : tokN (i₀ - 1) = y := by rw [htokN]; simp
  have htNlo : ∀ j, j < i₀ - 1 → tokN j = tok j := fun j hj => by
    rw [htokN]; simp [show j ≠ i₀ - 1 by omega, show ¬ i₀ ≤ j by omega]
  have htNhi : ∀ j, i₀ ≤ j → tokN j = coreTok j := fun j hj => by
    rw [htokN]; simp [show j ≠ i₀ - 1 by omega, hj]
  have hHL : ∀ j < i₀, out.mem (A.handleBase + j) = A.coreH j := fun j hj =>
    (hOHB j hj).trans (I.cells j (by omega)).2.2.1
  have hHS : ∀ j ≤ cfg.P.d, out.mem (A.handleBase + j) = s3.mem (A.handleBase + j) :=
    fun j hj => hKeepTS (A.handleBase + j) (.hb (by omega) (by omega))
  -- where the footprints of the new cores lie
  have hFootCls : ∀ j < cfg.P.d, ∀ a, Rcore.foot (out.mem (A.handleBase + j)) (tokN j) a →
      (j < i₀ - 1 ∧ Rcore.foot (A.coreH j) (tok j) a) ∨
      (j = i₀ - 1 ∧ ((Rcore.foot (A.coreH (i₀ - 1)) (tokM (i₀ - 1)) a ∧ a < s.regs 4) ∨
        (s3.regs 4 ≤ a ∧ a < ret))) ∨
      (i₀ ≤ j ∧ s.regs 4 ≤ a ∧ a < s3.regs 4 ∧
        Rcore.foot (s3.mem (A.handleBase + j)) (coreTok j) a) := by
    intro j hj a ha
    rcases Nat.lt_or_ge j (i₀ - 1) with hjl | hjg
    · rw [hHL j (by omega), htNlo j hjl] at ha
      exact Or.inl ⟨hjl, ha⟩
    · rcases Nat.lt_or_ge j i₀ with hjl' | hjg'
      · have hje : j = i₀ - 1 := by omega
        rw [hje, hHL (i₀ - 1) (by omega), htN1] at ha
        refine Or.inr (Or.inl ⟨hje, ?_⟩)
        rcases hFootY a ha with h | h
        · refine Or.inl ⟨h, ?_⟩
          rcases hTokM1 a h with h' | h'
          · have := (I.reps (i₀ - 1) hm1).2 a h'; omega
          · omega
        · exact Or.inr h
      · rw [hHS j hj.le, htNhi j hjg'] at ha
        have := (B.cores j hjg' hj).2.2.2.2 a ha
        exact Or.inr (Or.inr ⟨hjg', this.1, this.2, ha⟩)
  have hRepOut : ∀ j < cfg.P.d,
      Rcore.rep (out.mem (A.handleBase + j)) (chainLevelOrdAbs next j) (tokN j) out.mem := by
    intro j hj
    rcases Nat.lt_or_ge j (i₀ - 1) with hjl | hjg
    · rw [hHL j (by omega), htNlo j hjl, hAbsPre j (by omega)]
      have h := (M.reps j hj).1
      simp only [show ¬ i₀ ≤ j by omega, ↓reduceIte] at h
      rw [M.tokEq j (by omega)] at h
      exact (E.loc _ _ _ _ _ (fun a ha => (hLowLoc j hjl a ha).symm)).1 h
    · rcases Nat.lt_or_ge j i₀ with hjl' | hjg'
      · have hje : j = i₀ - 1 := by omega
        rw [hje, hHL (i₀ - 1) (by omega), htN1, hAbsPre (i₀ - 1) (by omega)]
        exact hRepY
      · rw [hHS j hj.le, htNhi j hjg']
        obtain ⟨_, _, _, hRepJ, hFootJ⟩ := B.cores j hjg' hj
        exact (E.loc _ _ _ _ _ (fun a ha =>
          (hKeepHigh a (hFootJ a ha).1 (hFootJ a ha).2).symm)).1 hRepJ
  have hFootOut : ∀ j < cfg.P.d, ∀ a, Rcore.foot (out.mem (A.handleBase + j)) (tokN j) a →
      Rcore.foot (A.coreH j) (tok j) a ∨ (sE.regs 4 ≤ a ∧ a < out.regs 4) := by
    intro j hj a ha
    rcases hFootCls j hj a ha with ⟨_, hf⟩ | ⟨he, hf⟩ | ⟨_, h1, h2, _⟩
    · exact Or.inl hf
    · subst he
      rcases hf with ⟨hf, _⟩ | ⟨h1, h2⟩
      · rcases hTokM1 a hf with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h'.1, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hDisjOut : ∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ ≠ j₂ → ∀ a,
      Rcore.foot (out.mem (A.handleBase + j₁)) (tokN j₁) a →
        ¬ Rcore.foot (out.mem (A.handleBase + j₂)) (tokN j₂) a := by
    intro j₁ hj₁ j₂ hj₂ hne a ha1 ha2
    rcases hFootCls j₁ hj₁ a ha1 with ⟨hl1, hf1⟩ | ⟨he1, hf1⟩ | ⟨hh1, hlo1, hhi1, hf1⟩ <;>
    rcases hFootCls j₂ hj₂ a ha2 with ⟨hl2, hf2⟩ | ⟨he2, hf2⟩ | ⟨hh2, hlo2, hhi2, hf2⟩
    · exact I.disj j₁ hj₁ j₂ hj₂ hne a hf1 hf2
    · rcases hf2 with ⟨hf2, _⟩ | ⟨h2a, _⟩
      · exact M.disj j₁ hj₁ (i₀ - 1) hm1 (by omega) a
          (by rw [M.tokEq j₁ (by omega)]; exact hf1) hf2
      · have := (I.reps j₁ hj₁).2 a hf1; omega
    · have := (I.reps j₁ hj₁).2 a hf1; omega
    · rcases hf1 with ⟨hf1, _⟩ | ⟨h1a, _⟩
      · exact M.disj (i₀ - 1) hm1 j₂ hj₂ (by omega) a hf1
          (by rw [M.tokEq j₂ (by omega)]; exact hf2)
      · have := (I.reps j₂ hj₂).2 a hf2; omega
    · omega
    · rcases hf1 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    · have := (I.reps j₂ hj₂).2 a hf2; omega
    · rcases hf2 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    · exact B.disj j₁ j₂ hh1 hj₁ hh2 hj₂ hne a hf1 hf2
  -- the slots: the slot of level `i₀ - 1` gets its descriptor again
  have hSlotLe : A.selBase + 1 + 12 * cfg.P.d ≤ A.heapFloor := by omega
  have hOther : ∀ r < cfg.P.d, r ≠ i₀ - 1 → ∀ x,
      Rcore.foot (out.mem (A.handleBase + r)) (tokN r) x →
      Rcore.foot (A.coreH r) (tok r) x ∨ (sE.regs 4 ≤ x ∧ x < s3.regs 4) := by
    intro r hr hne x hx
    rcases hFootCls r hr x hx with ⟨_, hf⟩ | ⟨he, _⟩ | ⟨_, hlo, hhi, _⟩
    · exact Or.inl hf
    · exact absurd he hne
    · exact Or.inr ⟨by omega, hhi⟩
  have hNew : ∀ x, Rcore.foot (out.mem (A.handleBase + (i₀ - 1))) (tokN (i₀ - 1)) x →
      Rcore.foot (A.coreH (i₀ - 1)) (tok (i₀ - 1)) x ∨
        (sE.regs 4 ≤ x ∧ x < s3.regs 4 + 5) := by
    intro x hx
    rw [hHL (i₀ - 1) (by omega), htN1] at hx
    rcases hFootY x hx with h | h
    · rcases hTokM1 x h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.1, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hKeepR : ∀ x < sE.regs 4, ¬ Rcore.foot (A.coreH (i₀ - 1)) (tok (i₀ - 1)) x →
      x ≠ A.selBase + 1 + 12 * (i₀ - 1) + 8 → x ≠ A.selBase + 1 + 12 * (i₀ - 1) + 9 →
      (A.heapFloor ≤ x ∨ (∃ r < i₀ - 1, Rcore.foot (A.coreH r) (tok r) x) ∨
        (A.selBase + 1 ≤ x ∧ x < A.selBase + 1 + 12 * cfg.P.d)) →
      out.mem x = sE.mem x := by
    intro x hx hnf h8x h9x hcase
    rcases hcase with hc | ⟨r, hr, hf⟩ | hc
    · refine hKeepAll x hx (fun j hj1 hj2 hfj => ?_) (Or.inr (by omega))
        ⟨by omega, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        (Or.inr (by omega)) (Or.inr (Or.inr hc))
      rcases Nat.lt_or_ge j i₀ with h | h
      · exact hnf (by rwa [show j = i₀ - 1 by omega] at hfj)
      · have := hFootOld j h hj2 x hfj; omega
    · obtain ⟨f1, f2, f3, f4, f5, f6⟩ :=
        branchBCoresDisjStatic_footSep I.static (r := r) (by omega) hf
      refine hKeepAll x hx (fun j _ hj2 hfj => I.disj r (by omega) j hj2 (by omega) x hf hfj)
        (f6 i₀ hLt) (.of_sep f1 f2 f3 f5 hLt) (f4.imp_left (fun h => by omega)) ?_
      rcases hFootLoc r (by omega) x hf with f7 | f7
      · exact Or.inl f7
      · exact Or.inr (Or.inr f7)
    · refine hKeepAll x hx (fun j _ hj2 hfj => ?_) (Or.inr (by omega))
        ⟨by omega, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
        (Or.inr (by omega)) (Or.inr (Or.inl ⟨by omega, hc.2, h8x, h9x⟩))
      rcases hFootLoc j hj2 x hfj with h | h <;> omega
  have hT0' : SelOutTableAt w (Rcore.foot (out.mem (A.handleBase + (i₀ - 1))) (tokN (i₀ - 1)))
      (s3.regs 4) (s3.regs 4 + 5) out.mem (s3.regs 4 + 5)
      (out.mem (A.selBase + 1 + 12 * (i₀ - 1) + 9)) (ch.G (i₀ - 1)).E := by
    rw [hHL (i₀ - 1) (by omega), htN1]; exact hT0
  have hT1' : SelOutTableAt w (Rcore.foot (out.mem (A.handleBase + (i₀ - 1))) (tokN (i₀ - 1)))
      (s3.regs 4) (s3.regs 4 + 5) out.mem (s3.regs 4 + 5 + 1)
      (out.mem (A.selBase + 1 + 12 * (i₀ - 1) + 9)) (ch.G (i₀ - 1)).E := by
    rw [hHL (i₀ - 1) (by omega), htN1]; exact hT1
  have hSlots : BranchBDoneSlots w P cfg.P.d
      (fun j => ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
      (fun r => Rcore.foot (out.mem (A.handleBase + r)) (tokN r)) A.heapFloor (out.regs 4)
      A.selBase out.mem i₀ D ch0.G levelU (fun j => (ch.G j).E)
      (fun j => (cfg.T.lsfs (ch.scState j) (ch.bran j)).wstr) := by
    have hDone := I.slots.of_le (n' := i₀ - 1) (by omega)
    have hLists := (I.slots (i₀ - 1) (by omega)).lists
    have hR := BranchBDoneSlots.refresh
      (foot' := fun r => Rcore.foot (out.mem (A.handleBase + r)) (tokN r)) (mem' := out.mem)
      (cur := s3.regs 4) (Lw := out.mem (A.selBase + 1 + 12 * (i₀ - 1) + 9)) hDone hLists
      hm1 hFloor (by omega) (fun r hr x => by simp only [hHL r (by omega), htNlo r hr])
      hOther hNew (fun r hr x hx => (I.reps r hr).2 x hx)
      (fun r hr hne x hx => I.disj r hr (i₀ - 1) hm1 hne x hx) hSlotLe
      (fun r hr i hi hf => by rcases hFootLoc r hr _ hf with h | h <;> omega) hKeepR
      h8 rfl h9 (by have h := hSV; rw [E.four, E.prec] at h; exact h) hT0' hT1'
    rwa [show i₀ - 1 + 1 = i₀ by omega, ← hout4] at hR
  have hCellsOut : ∀ j < cfg.P.d, out.mem (A.branchBase + j) = next.bran j ∧
      out.mem (A.ucBase + j) = next.updCount j ∧
      out.mem (A.rcBase + j) = next.rebuildCount j := by
    intro j hj
    obtain ⟨_, _, _, d4, _, _, _, _, d9, d10⟩ := I.cells j hj
    refine ⟨?_, ?_, ?_⟩
    · rcases Nat.lt_or_ge j i₀ with h | h
      · rw [hOBB j h, d4, (hPre j h).2.2.1]
      · rw [hKeepTS (A.branchBase + j) (.bb (by omega) (by omega))]
        exact (B.cores j h hj).1
    · rcases Nat.lt_or_ge j i₀ with h | h
      · rw [hOUC j h, d9, (hPre j h).2.2.2.1]
      · obtain ⟨_, _, _, hUpdNJ, _⟩ := hModelLevel j h hj
        rw [hUC0 j h hj, hUpdNJ]
    · by_cases h : j = i₀
      · rw [h, hKeepTS (A.rcBase + i₀) (.rc (by omega) (by omega)), h3RCi, M.rc, hRCN,
          ite_eq_left_of_eq_true _ _ (eq_self i₀)]
      · rw [hORC j hj h, d10, hRCN, ite_eq_right_of_eq_false _ _ (eq_false h)]
  have hLastB : out.mem (A.branchBase + cfg.P.d) = next.lastBran := by
    rw [hKeepTS (A.branchBase + cfg.P.d) (.bb (by omega) le_rfl)]; exact B.lastB
  have hGraphsOut : ∀ j < cfg.P.d,
      DynGraphAt out.mem (out.mem (A.levelMeta + cfg.P.d + j)) vCap eCap (next.G j) := by
    intro j hj
    rcases Nat.lt_or_ge j i₀ with h | h
    · have hGLtj : A.gPtr0 j + dynGraphSize vCap eCap ≤ A.selBase := S.gLt j hj
      rw [hOLMd j h.le, (I.cells j hj).2.2.2.2.2.2.1, (hPre j h).1]
      refine dynGraphAt_of_agree (I.graphs j hj) (fun x hx1 hx2 => ?_)
      obtain ⟨_, _, g3, g4, _, g6, g7, g8, g9⟩ := S.gSep j hj x hx1 hx2
      exact hKeepAll x (by omega) (fun r _ hr => (I.static r hr).2.2.2.2.1 j hj x hx1 hx2)
        ((g9 i₀ hLt).2 (by omega)) (.of_sep g3 g4 g6 (g7.imp_right Nat.le_of_lt) hLt)
        (g8.imp_left (fun h => by omega)) (Or.inl (by omega))
    · rcases Nat.lt_or_ge i₀ j with h' | h'
      · obtain ⟨hDG, hGLo, hGHi, _⟩ := B.graphs j h' hj
        rw [hKeepTS (A.levelMeta + cfg.P.d + j) (.lm (by omega) (by omega))]
        exact dynGraphAt_of_agree hDG (fun x hx1 hx2 => hKeepHigh x (by omega) (by omega))
      · have hji : j = i₀ := by omega
        rw [hji, hOLMd i₀ le_rfl, (I.cells i₀ hLt).2.2.2.2.2.2.1, hNG]
        refine dynGraphAt_of_agree M.graph (fun x hx1 hx2 => ?_)
        obtain ⟨_, _, g3, g4, _, g6, g7, g8, _⟩ := S.gSep i₀ hLt x hx1 hx2
        have hk : BranchBIntKeepCell cfg.P.d i₀ A x :=
          .of_sep g3 g4 g6 (g7.imp_right Nat.le_of_lt) hLt
        have hnf : ¬ Rcore.foot (A.coreH (i₀ - 1)) (tokM (i₀ - 1)) x := fun hf => by
          rcases hTokM1 x hf with h0 | h0
          · exact (I.static (i₀ - 1) hm1).2.2.2.2.1 i₀ hLt x hx1 hx2 h0
          · omega
        exact (hFrT x (by omega) hnf (g8.imp_left (fun h => by omega)) (by omega) (by omega)
          (by omega)).trans (B.frame x (by omega) hk.2.1 hk.2.2.1 hk.2.2.2 (Or.inl (by omega)))
  have hLensOut : ∀ j < cfg.P.d, EdgeValuesAt out.mem (out.mem (A.levelMeta + j)) 4 L P
      (next.G j).E (next.toTreeChain.chainLen next.ℓ j) := by
    intro j hj
    rcases Nat.lt_or_ge j i₀ with h | h
    · rw [hOLM j h.le, (I.cells j hj).2.2.2.2.2.2.2.1, (hPre j h).1, hLenPre j h]
      refine (I.lensLt j h).congr (fun e he t ht => ?_)
      have heL : e * L + L ≤ eCap * L := by
        simpa [Nat.succ_mul] using
          Nat.mul_le_mul_right L (Nat.succ_le_of_lt ((I.graphs j hj).2.2.1 e he))
      have hlo : A.lPtr0 j ≤ A.lPtr0 j + e * L + t := by omega
      have hhi : A.lPtr0 j + e * L + t < A.lPtr0 j + eCap * L := by omega
      obtain ⟨_, _, l3, l4, _, l6, l7, l8⟩ := S.lSep j hj _ hlo hhi
      have := S.lLt j hj
      refine hKeepAll (A.lPtr0 j + e * L + t) (by omega)
        (fun r _ hr => (I.static r hr).2.2.2.2.2 j hj _ hlo hhi) ?_
        (.of_sep l3 l4 l6 (l7.imp_right Nat.le_of_lt) hLt) (l8.imp_left (fun h => by omega))
        (Or.inl (by omega))
      by_contra hc
      simp only [not_or, not_lt, not_le] at hc
      obtain ⟨_, _, _, _, _, _, _, _, g9⟩ := S.gSep i₀ hLt _ hc.1 hc.2
      rcases (g9 j hj).1 with h | h <;> omega
    · rcases Nat.lt_or_ge i₀ j with h' | h'
      · obtain ⟨hDG, _, _, hEV, hLLo, hLHi, _⟩ := B.graphs j h' hj
        rw [hKeepTS (A.levelMeta + j) (.lm (by omega) (by omega))]
        refine hEV.congr (fun e he t ht => ?_)
        have heL : e * L + L ≤ eCap * L := by
          simpa [Nat.succ_mul] using
            Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hDG.2.2.1 e he))
        exact hKeepHigh (s3.mem (A.levelMeta + j) + e * L + t) (by omega) (by omega)
      · have hji : j = i₀ := by omega
        rw [hji, hOLM i₀ le_rfl, (I.cells i₀ hLt).2.2.2.2.2.2.2.1, hNG, hLenI]
        refine (I.lensEq hLt).congr (fun e he t ht => ?_)
        have heL : e * L + L ≤ eCap * L := by
          simpa [Nat.succ_mul] using
            Nat.mul_le_mul_right L (Nat.succ_le_of_lt (M.graph.2.2.1 e he))
        have hlo : A.lPtr0 i₀ ≤ A.lPtr0 i₀ + e * L + t := by omega
        have hhi : A.lPtr0 i₀ + e * L + t < A.lPtr0 i₀ + eCap * L := by omega
        obtain ⟨_, _, l3, l4, _, l6, l7, l8⟩ := S.lSep i₀ hLt _ hlo hhi
        have := S.lLt i₀ hLt
        refine hKeepAll (A.lPtr0 i₀ + e * L + t) (by omega)
          (fun r _ hr => (I.static r hr).2.2.2.2.2 i₀ hLt _ hlo hhi) ?_
          (.of_sep l3 l4 l6 (l7.imp_right Nat.le_of_lt) hLt) (l8.imp_left (fun h => by omega))
          (Or.inl (by omega))
        by_contra hc
        simp only [not_or, not_lt, not_le] at hc
        obtain ⟨_, _, _, _, _, _, _, _, g9⟩ := S.gSep i₀ hLt _ hc.1 hc.2
        rcases (g9 i₀ hLt).1 with h | h <;> omega
  -- the new last level
  have hHd : out.mem (A.handleBase + cfg.P.d) = s3.mem (A.handleBase + cfg.P.d) :=
    hHS cfg.P.d le_rfl
  have hLastRepOut :
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (next.G cfg.P.d).E).rep
        (out.mem (A.handleBase + cfg.P.d)) (next.lastK, next.lastLSFs) termTokN out.mem := by
    rw [hHd]
    exact (LastLevelProgram.lastLevelRepresentation_local vCap eCap 4 L P (next.G cfg.P.d).E
      _ _ _ s3.mem out.mem (fun a ha =>
        (hKeepHigh a (B.lastFoot a ha).1 (B.lastFoot a ha).2.1).symm)).1 B.lastRep
  have hLastFootOut : ∀ a, (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P
      (next.G cfg.P.d).E).foot (out.mem (A.handleBase + cfg.P.d)) termTokN a →
      sE.regs 4 ≤ a ∧ a < out.regs 4 ∧
      ∀ j < cfg.P.d, ¬ Rcore.foot (out.mem (A.handleBase + j)) (tokN j) a := by
    intro a ha
    rw [hHd] at ha
    obtain ⟨ha1, ha2, ha3⟩ := B.lastFoot a ha
    refine ⟨by omega, by omega, fun j hj hf => ?_⟩
    rcases hFootCls j hj a hf with ⟨_, hf'⟩ | ⟨_, hf'⟩ | ⟨hj', _, _, hf'⟩
    · have := (I.reps j hj).2 a hf'; omega
    · rcases hf' with ⟨_, h⟩ | ⟨h, _⟩ <;> omega
    · exact ha3 j hj' hj hf'
  -- the old forests
  have hOldFOut : ForestPtrListAt out.mem (oldPtrs + i₀) (chainSuffixForests ch0 i₀) intCap
      (out.regs 4) := by
    refine ⟨by rw [chainSuffixForests_length]; omega, fun t ht => ?_⟩
    have ht' := ht
    rw [chainSuffixForests_length] at ht'
    by_cases htLt : t < cfg.P.d - i₀
    · rw [chainSuffixForests_getElem_lt ch0 htLt]
      obtain ⟨vc, ec, hDG, hEnd, hFt⟩ := M.oldF (i₀ + t) (by omega) (by omega)
      have hSub : oldPtrs + i₀ + t = oldPtrs + (i₀ + t) := by omega
      have hPtr : out.mem (oldPtrs + (i₀ + t)) = s.mem (oldPtrs + (i₀ + t)) :=
        (hKeepMid _ (by omega) (by omega)).trans
          (B.frame _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
            ⟨Or.inr (by omega), Or.inr (by omega)⟩ (Or.inl (by omega)))
      rw [hSub, hPtr]
      refine ⟨vc, ec, dynGraphAt_of_agree hDG (fun x hx1 hx2 => ?_), by omega,
        hOldFCap (i₀ + t) (by omega) (by omega)⟩
      have hf := hFt x hx1 hx2
      have hnf : ¬ Rcore.foot (A.coreH (i₀ - 1)) (tokM (i₀ - 1)) x :=
        M.disj (i₀ + t) (by omega) (i₀ - 1) hm1 (by omega) x hf
      rcases (M.reps (i₀ + t) (by omega)).2 x hf with h0 | ⟨_, h2⟩
      · have hsel := hFootOld (i₀ + t) (by omega) (by omega) x h0
        obtain ⟨f1, f2, f3, f4, f5, _⟩ :=
          branchBCoresDisjStatic_footSep I.static (r := i₀ + t) (by omega) h0
        have hk : BranchBIntKeepCell cfg.P.d i₀ A x := .of_sep f1 f2 f3 f5 hLt
        exact (hFrT x (by omega) hnf (f4.imp_left (fun h => by omega)) (by omega) (by omega)
          (by omega)).trans (B.frame x (by omega) hk.2.1 hk.2.2.1 hk.2.2.2 (Or.inl (by omega)))
      · exact (hFrT x (by omega) hnf (Or.inr (by omega)) (by omega) (by omega) (by omega)).trans
          (B.frame x h2 (Or.inr (by omega)) (Or.inr (by omega))
            ⟨Or.inr (by omega), Or.inr (by omega)⟩ (Or.inr (by omega)))
    · have htEq : t = cfg.P.d - i₀ := by omega
      subst htEq
      rw [chainSuffixForests_getElem_last]
      obtain ⟨vc, ec, hDG, hFt⟩ := hOldLast
      have hSub : oldPtrs + i₀ + (cfg.P.d - i₀) = oldPtrs + cfg.P.d := by omega
      have hPtr : out.mem (oldPtrs + cfg.P.d) = sE.mem (oldPtrs + cfg.P.d) :=
        (hKeepMid _ (by omega) (by omega)).trans
          ((B.frame _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
            ⟨Or.inr (by omega), Or.inr (by omega)⟩ (Or.inl (by omega))).trans
            (M.frame _ (by omega)
              (fun j _ hj hf => by rcases hFootLoc j hj _ hf with h | h <;> omega)
              (Or.inr (by omega)) (by omega) (Or.inr (by omega))))
      rw [hSub, hPtr]
      have hBlk : ∀ x, sE.mem (oldPtrs + cfg.P.d) ≤ x →
          x < sE.mem (oldPtrs + cfg.P.d) + dynGraphSize vc ec →
          x < A.selBase ∧ out.mem x = sE.mem x := fun x hx1 hx2 => by
        obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := I.term.2 x (hFt x hx1 hx2)
        exact ⟨t1, hKeepAll x (by omega) (fun j _ hj => t2 j hj) (t3 i₀ hLt).1
          (.of_sep t4 t5 t6 (t8.imp_right Nat.le_of_lt) hLt) (t7.imp_left (fun h => by omega))
          (Or.inl t1)⟩
      have hSz : 0 < dynGraphSize vc ec := by unfold dynGraphSize; omega
      have hEndLt := (hBlk (sE.mem (oldPtrs + cfg.P.d) + dynGraphSize vc ec - 1) (by omega)
        (by omega)).1
      exact ⟨vc, ec, dynGraphAt_of_agree hDG (fun x hx1 hx2 => (hBlk x hx1 hx2).2), by omega,
        hOldLastFCap⟩
  -- the new forests
  have hNewFOut : ForestPtrListAt out.mem (newPtrs + i₀) (chainSuffixForests next i₀) intCap
      (out.regs 4) :=
    B.newF.congr_from B.newFLo (fun t ht => by
        rw [chainSuffixForests_length] at ht
        exact hKeepMid _ (by omega) (by omega))
      (fun a h1 h2 => hKeepHigh a h1 h2) (by omega)
  -- the frame below the select base
  have hFrameOut : ∀ a < A.selBase, (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) a) →
      (a < A.handleBase ∨ A.handleBase + cfg.P.d < a) →
      (a < A.branchBase ∨ A.branchBase + cfg.P.d < a) →
      (a < A.levelMeta ∨ A.levelMeta + 2 * cfg.P.d ≤ a) →
      (a < A.rcBase ∨ A.rcBase + cfg.P.d ≤ a) →
      (∀ j < cfg.P.d, a < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ a) →
      (a < A.ucBase ∨ A.ucBase + cfg.P.d ≤ a) → out.mem a = sE.mem a :=
    fun a ha hc h1 h2 h3 h4 hg hu => hKeepAll a (by omega) (fun j _ hj => hc j hj) (hg i₀ hLt)
      (.of_sep h1 h2 h3 h4 hLt) (hu.imp_left (fun h => by omega)) (Or.inl ha)
  have hFrameHeap : ∀ a, A.selBase + 1 + 12 * cfg.P.d ≤ a → a < A.heapFloor →
      (a < oldPtrs ∨ oldPtrs + (cfg.P.d + 1) ≤ a) →
      (a < newPtrs ∨ newPtrs + (cfg.P.d + 1) ≤ a) → out.mem a = sE.mem a :=
    fun a h1 h2 ho hn => (hKeepMid a h1 h2).trans (hKeep3 a (by omega)
      (fun j _ hj hf => by rcases hFootLoc j hj a hf with h | h <;> omega) (Or.inr (by omega))
      (.of_sep (by omega) (by omega) (by omega) (by omega) hLt)
      (ho.elim (fun _ => Or.inl (by omega)) fun _ => Or.inr (by omega))
      (hn.imp_left fun _ => by omega))
  have hRegsOut : ∀ r, 70 ≤ r → r ≠ 97 → r ≠ 99 → out.regs r = sE.regs r :=
    fun r h70 h97 h99 =>
      (hregsT r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) h97).trans
        (hR3 r h70 h99)
  -- the costs
  have hSplitOut := sum_range_split3
    (fun j => Rcore.phi (out.mem (A.handleBase + j)) (tokN j) out.mem) (m := i₀ - 1)
    (d := cfg.P.d) (by omega)
  have hSplitS := sum_range_split3 (fun j => Rcore.phi (A.coreH j) (tokM j) s.mem)
    (m := i₀ - 1) (d := cfg.P.d) (by omega)
  rw [show i₀ - 1 + 1 = i₀ by omega] at hSplitOut hSplitS
  have hLowSum : (Finset.range (i₀ - 1)).sum
        (fun j => Rcore.phi (out.mem (A.handleBase + j)) (tokN j) out.mem) =
      (Finset.range (i₀ - 1)).sum (fun j => Rcore.phi (A.coreH j) (tokM j) s.mem) :=
    Finset.sum_congr rfl (fun j hj => by
      have hj' := Finset.mem_range.mp hj
      rw [hHL j (by omega), htNlo j hj', ← M.tokEq j (by omega)]
      exact (E.loc _ (chainLevelOrdAbs ch j) _ _ _ (fun a ha =>
        (hLowLoc j hj' a (by rwa [M.tokEq j (by omega)] at ha)).symm)).2.symm)
  have hHighSum : (Finset.Ico i₀ cfg.P.d).sum
        (fun j => Rcore.phi (out.mem (A.handleBase + j)) (tokN j) out.mem) =
      (Finset.Ico i₀ cfg.P.d).sum
        (fun j => Rcore.phi (s3.mem (A.handleBase + j)) (coreTok j) s3.mem) :=
    Finset.sum_congr rfl (fun j hj => by
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      obtain ⟨_, _, _, _, hFootJ⟩ := B.cores j hj1 hj2
      rw [hHS j hj2.le, htNhi j hj1]
      exact (E.loc _ (chainLevelOrdAbs next j) _ _ _ (fun a ha =>
        (hKeepHigh a (hFootJ a ha).1 (hFootJ a ha).2).symm)).2.symm)
  have hMidOut : Rcore.phi (out.mem (A.handleBase + (i₀ - 1))) (tokN (i₀ - 1)) out.mem =
      Rcore.phi (A.coreH (i₀ - 1)) y out.mem := by rw [hHL (i₀ - 1) (by omega), htN1]
  have hΦ : branchBPhiSum Rcore A tokM s.mem =
      (Finset.range cfg.P.d).sum (fun j => Rcore.phi (A.coreH j) (tokM j) s.mem) := rfl
  have hφ1 := hLoc1.2
  have hRuns : Runs w p ω (wireBranchBIntKFBL dgApply initCore (opCore 3) (opCore 2) coreLenProc
      (opCore 5) lastInit) st .normal out (c1 + (c2 + c3 + 1) + 1) := by
    unfold wireBranchBIntKFBL
    exact runs_seq_iff.mpr (Or.inr ⟨s, c1, c2 + c3 + 1, r1,
      runs_seq_iff.mpr (Or.inr ⟨s3, c2, c3, r2, r3, rfl⟩), rfl⟩)
  refine ⟨out, c1 + (c2 + c3 + 1) + 1, termTokN, tokN, hRuns, by omega,
    { heapLo := by omega
      zero := by rw [hout4]; exact hzOut
      r97 := hout97, regs := hRegsOut
      handlesLow := hHL
      reps := fun j hj => ⟨hRepOut j hj, hFootOut j hj⟩
      disj := hDisjOut
      slots := hSlots
      sel := hSel
      cells := hCellsOut
      lastB := hLastB
      graphs := hGraphsOut
      lens := hLensOut
      lastRep := hLastRepOut
      lastFoot := hLastFootOut
      oldF := hOldFOut
      newF := hNewFOut
      frame := hFrameOut, frameHeap := hFrameHeap }, ?_⟩
  rw [hSplitOut, hLowSum, hMidOut, hHighSum]; omega

end MinCostFlow.MinRatio

end
