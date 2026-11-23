module

public import MinCostFlow.MinRatio.WireChainCoreBranchBIntRebNewKFBL
import WordRAM.Tactic

/-!
# Suffix rebuild and new-forest collection with last-level disjointness (`WireChainCoreBranchBExitLayIntReb`)

`wireBranchBIntRebNewKFBL_runs` (`WireChainCoreBranchBIntRebNewKFBL.lean`) produces
`BranchBIntRebKFBL`, which omits the last-level disjointness clauses for the new level blocks
(`i₀ + 1 ≤ j < d`) that `wireBranchBIntRebKFBL_runs` (`WireChainCoreBranchBIntRebKFBL.lean`)
already proves. This file composes `wireBranchBIntRebKFBL_runs` and `wireBranchBIntNewKFBL_runs`
while retaining those two clauses (`wireBranchBIntRebNewKFBL_runs_lay`), so that the interior-exit
layout proof (`BranchBIntExitLayGoalKFBL`) can establish `BranchBExitLayKFBL.metaNew`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

set_option maxHeartbeats 1600000 in
/-- Like `wireBranchBIntRebNewKFBL_runs`, additionally preserving the disjointness of the new
level length and graph blocks (`i₀ + 1 ≤ j < cfg.P.d`) from the footprint of the new last level. -/
theorem wireBranchBIntRebNewKFBL_runs_lay
    {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy N0 oldPtrs newPtrs intCap i₀ ordPtr ordWords wordExp
      stretchPrec capLimit coreLenProc lastInit lastMul lastSpace : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {opCore opLast : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ}
    {ℓ' g' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ}
    {ch : ChainState cfg.T cfg.P} {curG : MGraph} {curU : List Update}
    {curEditsList : List OrdEdit} {curEnc : ℕ} {oldOrd : ℕ → List End} {sE s : State}
    {tok tokM : ℕ → Rcore.τ} {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists} {levelSpace levelCost : ℕ → ℕ}
    (E : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore
      p opCore)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hOldLo : A.selBase + 1 + 12 * cfg.P.d ≤ oldPtrs)
    (hOldHi : oldPtrs + (cfg.P.d + 1) ≤ A.heapFloor)
    (hNewLo : A.selBase + 1 + 12 * cfg.P.d ≤ newPtrs)
    (hNewHi : newPtrs + (cfg.P.d + 1) ≤ A.heapFloor)
    (hPos : 0 < i₀) (hLt : i₀ < cfg.P.d)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
      EWc ULc ch0 termTok i₀ ch curG curU curEditsList oldOrd sE tok curBatch curBatchWords
      curEdits curEditsWords levelU levelUS D)
    (M : BranchBIntMidKFBL (w := w) (vCap := vCap) (eCap := eCap) A oldPtrs i₀ ch0 ch curG sE s
      tok tokM ordPtr ordWords)
    (h71 : sE.regs 71 = 0) (h81 : sE.regs 81 = newPtrs)
    (next : ChainState cfg.T cfg.P)
    (hNext : next = (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
      { ch with ℓ := ℓ', g := g' } i₀ curG curEnc).1)
    (hReb : UpdateRebuildModelInv w L P wordExp stretchPrec ch i₀ curG ℓ' g' curEnc)
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
    (hRoom : s.regs 4 + (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace + 5 * (cfg.P.d - i₀) <
      2 ^ w) :
    ∃ (s3 : State) (cost termTokN : ℕ) (coreTok : ℕ → Rcore.τ),
      Runs w p ω
        (wireBranchBIntSuffixKFBL initCore (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
          wireBranchBIntNewStmt (opCore 2))
        s .normal s3 cost ∧
      s3.regs 4 ≤ s.regs 4 + (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace +
        5 * (cfg.P.d - i₀) ∧
      BranchBIntRebKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap) A newPtrs intCap
        i₀ next s s3 coreTok termTokN ∧
      (∀ j, i₀ + 1 ≤ j → j < cfg.P.d →
        (∀ a, s3.mem (A.levelMeta + j) ≤ a → a < s3.mem (A.levelMeta + j) + eCap * L →
          ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P
            (next.G cfg.P.d).E).foot (s3.mem (A.handleBase + cfg.P.d)) termTokN a) ∧
        (∀ a, s3.mem (A.levelMeta + cfg.P.d + j) ≤ a →
          a < s3.mem (A.levelMeta + cfg.P.d + j) + dynGraphSize vCap eCap →
          ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P
            (next.G cfg.P.d).E).foot (s3.mem (A.handleBase + cfg.P.d)) termTokN a)) ∧
      cost + (Finset.Ico i₀ cfg.P.d).sum
          (fun j => Rcore.phi (s3.mem (A.handleBase + j)) (coreTok j) s3.mem) ≤
        (Finset.Ico i₀ cfg.P.d).sum (fun j => levelCost j + 9) +
          lastMul * (cfg.L.cost (next.G cfg.P.d) + 1) + (cfg.P.d - i₀) * (Psc.readout + 48) +
          140 := by
  obtain ⟨hFloor, _, _, _, _, _, _, _, hr75, _, hr77, hr78, _, hr83, _, _, _, _, hr96, _, _,
    _⟩ := I.regs
  obtain ⟨s2, c2, termTokN, coreTok2, r2, hR2, h2lo, h2hi, hz2, hCores2, hDisj2, hGr2, hLB2,
      hLH2, hLRep2, hLFoot2, hLDisj2, hFr2, hc2⟩ :=
    wireBranchBIntRebKFBL_runs (ω := ω) E S hOldLo hOldHi hPos hLt I M next hNext hReb
      hWordExpEq hInitOrdEq hNextN hNextRot hImpl hcapLim hCoreLenProc hLastImpl hLevelSpaceDom
      hLevelCostDom hLastSpaceDom hLWord hPWord hWidth hDepthW hNW (by omega)
  obtain ⟨_, hNG, _, _, _, _, _, _, _, _, _, hModelLevel, hModelLast⟩ :=
    branchBIntNext_facts (fmt := fmt) (Psc := Psc) ch curG ℓ' g' curEnc i₀ next hNext hPos hLt
      hReb hWordExpEq E.prec hInitOrdEq hNextN hNextRot
  have hLastKPos : 0 < next.lastK := by subst hNext; exact hReb.2.1
  have hLastBr0 : next.lastBran = 0 := hModelLast.2.1
  have hHBLt := S.hbLt
  have hBBLt := S.bbLt
  have hMetaLt := S.metaLt
  have hRCLM := S.sepRCLM
  have hGLt := S.gLt i₀ hLt
  have hsE4 : sE.regs 4 < s.regs 4 := by have := M.heapLo; have := M.ord.2.2.1; omega
  have hR (r : ℕ) (h70 : 70 ≤ r) (h99 : r ≠ 99) : s2.regs r = sE.regs r :=
    (hR2 r h70).trans (M.regs r h70 h99)
  have hkPos : 0 < cfg.P.k := by have := (I.cells i₀ hLt).2.2.2.2.1; omega
  obtain ⟨_, _, _, _, _, _, c7, _, _, _⟩ := I.cells i₀ hLt
  have hSepHL := S.sepHL
  have hSepBL := S.sepBL
  have hNotG : ¬ (A.gPtr0 i₀ ≤ A.levelMeta + cfg.P.d + i₀ ∧
      A.levelMeta + cfg.P.d + i₀ < A.gPtr0 i₀ + dynGraphSize vCap eCap) := fun ⟨h1, h2⟩ => by
    obtain ⟨_, _, _, _, _, g6, _⟩ := S.gSep i₀ hLt _ h1 h2; omega
  have hCellG : s2.mem (A.levelMeta + cfg.P.d + i₀) = A.gPtr0 i₀ := by
    rw [hFr2 _ (by omega) (by omega) (by omega) ⟨by omega, by omega⟩,
      M.frame _ (by omega) (fun r _ hr => ((I.static r hr).2.2.2.1 i₀ hLt).2.2.1)
        (by omega) (by omega) (Or.inl (by omega)), c7]
  have hG2 : DynGraphAt s2.mem (A.gPtr0 i₀) vCap eCap (next.G i₀) := by
    rw [hNG]
    exact dynGraphAt_of_agree M.graph (fun a h1 h2 => by
      obtain ⟨_, _, g3, g4, _, g6, _⟩ := S.gSep i₀ hLt a h1 h2
      exact hFr2 a (by omega) (by omega) (by omega) ⟨by omega, by omega⟩)
  have hLRep2' := hLRep2
  obtain ⟨hTLo, _, _, hTBr⟩ := hLRep2'
  obtain ⟨hTBrHdr, hTLSF⟩ := hTBr next.lastBran (by rw [hLastBr0]; exact hLastKPos)
  set termH := s2.mem (A.handleBase + cfg.P.d) with htermH
  set lsfHdr := s2.mem (termH + 1 + next.lastBran) with hlsfHdr
  set forestPtr := s2.mem (lsfHdr + 1) with hforestPtr
  have hInT : ∀ a, termH ≤ a → a < termTokN → s.regs 4 ≤ a ∧ a < s2.regs 4 := fun a h1 h2 =>
    hLFoot2 a ⟨h1, h2⟩
  have hTermEndLe : termTokN ≤ s2.regs 4 := by
    have := (hInT (termTokN - 1) (by omega) (by omega)).2; omega
  obtain ⟨hB1, hB2, _, _, hB5, hB6, _⟩ := hTBrHdr
  have hTLo' : termH + 1 + next.lastK ≤ termTokN := hTLo
  have hB1' : termH ≤ lsfHdr := le_trans (by omega) hB1
  have hB5' : termH ≤ forestPtr := le_trans (by omega) hB5
  obtain ⟨s3, c3, coreTok3, r3, h3lo, h3hi, hz3, hForest3, hForestLo3, hCores3, hDisj3, hFr3,
      hR3, hc3⟩ :=
    wireBranchBIntNewKFBL_runs (w := w) (L := L) (depth := depth) (vCap := vCap) (eCap := eCap)
      (capExp := capExp) (i0 := i₀) (handleBase := A.handleBase) (branchBase := A.branchBase)
      (levelMeta := A.levelMeta) (newPtrs := newPtrs) (intCap := intCap) (termHandle := termH)
      (lo := s.regs 4)
      (vcLast := vCap) (ecLast := eCap) (lsfHdr := lsfHdr) (forestPtr := forestPtr)
      (fmt := fmt) (T := cfg.T) (CP := cfg.P) (P := Psc) (allocation := alloc) (Rcore := Rcore)
      (p := p) (op := opCore) (st := s2) (ω := ω) next (fun j => s2.mem (A.handleBase + j))
      coreTok2 E.loc hLt
      ((hR 96 (by decide) (by decide)).trans hr96) ((hR 71 (by decide) (by decide)).trans h71)
      ((hR 75 (by decide) (by decide)).trans hr75) ((hR 77 (by decide) (by decide)).trans hr77)
      ((hR 78 (by decide) (by decide)).trans hr78) ((hR 81 (by decide) (by decide)).trans h81)
      ((hR 83 (by decide) (by decide)).trans hr83) E.kW E.dW (by have := E.w16; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hz2
      (fun j hj1 hj2 => (hImpl j hj1 hj2).2)
      (fun j hj1 hj2 => by
        obtain ⟨hBrJ, hHLoJ, hHHiJ, hRepJ, hFootJ⟩ := hCores2 j hj1 hj2
        obtain ⟨hScJ, _, hBrNJ, hUpdNJ, hmLeJ, hnLeJ, _, _, hRotJ, hPosJ, _⟩ :=
          hModelLevel j hj1 hj2
        have hDGJ :
            DynGraphAt s2.mem (s2.mem (A.levelMeta + cfg.P.d + j)) vCap eCap (next.G j) ∧
            s2.mem (A.levelMeta + cfg.P.d + j) + dynGraphSize vCap eCap ≤ s2.regs 4 ∧
            ∀ a, s2.mem (A.levelMeta + cfg.P.d + j) ≤ a →
              a < s2.mem (A.levelMeta + cfg.P.d + j) + dynGraphSize vCap eCap →
              (∀ r, i₀ ≤ r → r < cfg.P.d →
                ¬ Rcore.foot (s2.mem (A.handleBase + r)) (coreTok2 r) a) ∧
              (a < newPtrs + i₀ ∨ newPtrs + (cfg.P.d + 1) ≤ a) := by
          by_cases hji : j = i₀
          · subst hji
            rw [hCellG]
            exact ⟨hG2, by omega, fun a h1 h2 => ⟨fun r hr1 hr2 hf => by
              have := (hCores2 r hr1 hr2).2.2.2.2 a hf; omega, Or.inl (by omega)⟩⟩
          · obtain ⟨hDG, hGLo, hGHi, _, _, _, hDisjC, _, _⟩ := hGr2 j (by omega) hj2
            exact ⟨hDG, hGHi, fun a ha1 ha2 =>
              ⟨fun r hr1 hr2 => (hDisjC r hr1 hr2).2 a ha1 ha2, Or.inr (by omega)⟩⟩
        have hInJ : SparseCoreOrdInput cfg.T cfg.P.k (next.lvlM j) next.N₀ (next.scState j)
            (next.G j) (next.levelOrd j) (next.updCount j) := by
          rw [hScJ, hUpdNJ]
          exact SparseCoreOrdInput.init (next.G j) _ _ (next.levelOrd j) hDGJ.1.1 hmLeJ hnLeJ
            (fun e he => by simp [he, hPosJ e he]) hRotJ
        exact ⟨rfl, hBrJ, by rw [hBrNJ]; exact hkPos, by omega, hRepJ, hInJ,
          fun a ha => (hFootJ a ha).2,
          fun r hr1 hr2 => ⟨fun hf => by have := ((hCores2 r hr1 hr2).2.2.2.2 _ hf).1; omega,
            fun hf => by have := ((hCores2 r hr1 hr2).2.2.2.2 _ hf).1; omega,
            fun hf => by have := ((hCores2 r hr1 hr2).2.2.2.2 _ hf).1; omega⟩,
          Or.inl (by omega), Or.inl (by omega), Or.inl (by omega),
          fun t _ _ hf => by have := (hFootJ _ hf).1; omega, hDGJ⟩)
      hDisj2 rfl hLB2 rfl rfl hTLSF.2.1 (le_trans hB6 hTermEndLe) hLastFCap
      ⟨Or.inl (by omega), Or.inl (by omega),
        Or.inr (by have := (hInT (termH + 1 + next.lastBran) (by omega) (by omega)).1; omega),
        Or.inr (by have := (hInT (lsfHdr + 1) (by omega) (by omega)).1; omega),
        (hInT _ (by omega) (by omega)).2, (hInT _ (by omega) (by omega)).2,
        fun r hr1 hr2 => ⟨fun hf => by have := ((hCores2 r hr1 hr2).2.2.2.2 _ hf).1; omega,
          fun hf => by have := ((hCores2 r hr1 hr2).2.2.2.2 _ hf).1; omega,
          hLDisj2 r hr1 hr2 _ ⟨by omega, by omega⟩, hLDisj2 r hr1 hr2 _ ⟨by omega, by omega⟩⟩,
        fun a ha1 ha2 => ⟨fun r hr1 hr2 => hLDisj2 r hr1 hr2 a ⟨by omega, by omega⟩,
          Or.inr (by have := (hInT a (by omega) (by omega)).1; omega)⟩⟩
      hFCap (fun j hj1 hj2 a ha => ((hCores2 j hj1 hj2).2.2.2.2 a ha).1) h2lo
      (le_trans hLH2 hB5')
  have hKeep3 : ∀ a < s2.regs 4,
      (∀ j, i₀ ≤ j → j < cfg.P.d → ¬ Rcore.foot (s2.mem (A.handleBase + j)) (coreTok2 j) a) →
      (a < newPtrs + i₀ ∨ newPtrs + (cfg.P.d + 1) ≤ a) → s3.mem a = s2.mem a :=
    fun a ha hn ho => hFr3 a ha hn ho
  have hKeepLow : ∀ a < s.regs 4, (a < newPtrs + i₀ ∨ newPtrs + (cfg.P.d + 1) ≤ a) →
      s3.mem a = s2.mem a := fun a ha ho =>
    hKeep3 a (by omega) (fun j hj1 hj2 hf => by
      have := ((hCores2 j hj1 hj2).2.2.2.2 a hf).1; omega) ho
  have hHC : ∀ j ≤ cfg.P.d, s3.mem (A.handleBase + j) = s2.mem (A.handleBase + j) :=
    fun j hj => hKeepLow _ (by omega) (Or.inl (by omega))
  have hBC : ∀ j ≤ cfg.P.d, s3.mem (A.branchBase + j) = s2.mem (A.branchBase + j) :=
    fun j hj => hKeepLow _ (by omega) (Or.inl (by omega))
  have hMC : ∀ j < 2 * cfg.P.d, s3.mem (A.levelMeta + j) = s2.mem (A.levelMeta + j) :=
    fun j hj => hKeepLow _ (by omega) (Or.inl (by omega))
  have hC3 : ∀ j, i₀ ≤ j → j < cfg.P.d →
      Rcore.rep (s3.mem (A.handleBase + j)) (chainLevelOrdAbs next j) (coreTok3 j) s3.mem ∧
      (∀ a, Rcore.foot (s3.mem (A.handleBase + j)) (coreTok3 j) a →
        Rcore.foot (s2.mem (A.handleBase + j)) (coreTok2 j) a ∨
          (s2.regs 4 ≤ a ∧ a < s3.regs 4)) := fun j hj1 hj2 => by
    rw [hHC j (by omega)]; exact hCores3 j hj1 hj2
  have hHigh : ∀ a, s.regs 4 ≤ a → a < s2.regs 4 →
      (∀ j, i₀ ≤ j → j < cfg.P.d → ¬ Rcore.foot (s2.mem (A.handleBase + j)) (coreTok2 j) a) →
      s3.mem a = s2.mem a := fun a h1 h2 hn => hKeep3 a h2 hn (Or.inr (by omega))
  refine ⟨s3, c2 + c3 + 1, termTokN, coreTok3, runs_seq_iff.mpr (Or.inr ⟨s2, c2, c3, r2, r3, rfl⟩),
    by omega, ?_, ?_, ?_⟩
  · refine
      { regs := fun r h70 => (hR3 r h70).trans (hR2 r h70)
        heapLo := h2lo.trans h3lo
        zero := hz3
        cores := fun j hj1 hj2 => ?_
        disj := fun j₁ j₂ h1 h2 h3 h4 hne a ha1 ha2 => ?_
        graphs := fun j hj1 hj2 => ?_
        lastB := (hBC _ le_rfl).trans hLB2
        lastH := by rw [hHC _ le_rfl]; exact hLH2
        lastRep := ?_
        lastFoot := fun a ha => ?_
        newF := hForest3
        newFLo := hForestLo3
        frame := fun a ha hh hb hl hn => (hKeepLow a ha hn).trans (hFr2 a ha hh hb hl) }
    · obtain ⟨hBrJ, hHLoJ, hHHiJ, _, hFootJ⟩ := hCores2 j hj1 hj2
      refine ⟨(hBC j (by omega)).trans hBrJ, by rw [hHC j (by omega)]; exact hHLoJ,
        by rw [hHC j (by omega)]; omega, (hC3 j hj1 hj2).1, fun a ha => ?_⟩
      rcases (hC3 j hj1 hj2).2 a ha with h | h
      · have := hFootJ a h; omega
      · omega
    · rw [hHC j₁ (by omega)] at ha1
      rw [hHC j₂ (by omega)] at ha2
      exact hDisj3 j₁ j₂ h1 h2 h3 h4 hne a ha1 ha2
    · obtain ⟨hDG, hGLo, hGHi, hEV, hLLo, hLHi, hDisjC, _, _⟩ := hGr2 j hj1 hj2
      have hcG : s3.mem (A.levelMeta + cfg.P.d + j) = s2.mem (A.levelMeta + cfg.P.d + j) := by
        rw [Nat.add_assoc]; exact hMC _ (by omega)
      have hcL : s3.mem (A.levelMeta + j) = s2.mem (A.levelMeta + j) := hMC _ (by omega)
      have hOff3 : ∀ r, i₀ ≤ r → r < cfg.P.d → ∀ a, a < s2.regs 4 →
          ¬ Rcore.foot (s2.mem (A.handleBase + r)) (coreTok2 r) a →
          ¬ Rcore.foot (s3.mem (A.handleBase + r)) (coreTok3 r) a := fun r hr1 hr2 a ha hn hf => by
        rcases (hC3 r hr1 hr2).2 a hf with h | h
        · exact hn h
        · omega
      rw [hcG, hcL]
      refine ⟨dynGraphAt_of_agree hDG (fun a h1 h2 => hHigh a (by omega) (by omega)
          (fun r hr1 hr2 => (hDisjC r hr1 hr2).2 a h1 h2)), hGLo, by omega, ?_, hLLo, by omega,
        fun r hr1 hr2 =>
          ⟨fun a h1 h2 => hOff3 r hr1 hr2 a (by omega) ((hDisjC r hr1 hr2).1 a h1 h2),
            fun a h1 h2 => hOff3 r hr1 hr2 a (by omega) ((hDisjC r hr1 hr2).2 a h1 h2)⟩⟩
      rw [← E.prec]
      refine hEV.congr (fun e he t ht => ?_)
      have heL : e * L + L ≤ eCap * L := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hDG.2.2.1 e he))
      exact hHigh _ (by omega) (by omega)
        (fun r hr1 hr2 => (hDisjC r hr1 hr2).1 _ (by omega) (by omega))
    · rw [hHC _ le_rfl, ← E.prec]
      exact (LastLevelProgram.lastLevelRepresentation_local vCap eCap 4 L fmt.precision
        (next.G cfg.P.d).E termH (next.lastK, next.lastLSFs) termTokN s2.mem s3.mem
        (fun a ha => (hHigh a (hInT a ha.1 ha.2).1 (hInT a ha.1 ha.2).2
          (fun r hr1 hr2 => hLDisj2 r hr1 hr2 a ha)).symm)).1 hLRep2
    · rw [hHC _ le_rfl] at ha
      obtain ⟨ha1, ha2⟩ := hInT a ha.1 ha.2
      refine ⟨ha1, by omega, fun j hj1 hj2 hf => ?_⟩
      rcases (hC3 j hj1 hj2).2 a hf with h | h
      · exact hLDisj2 j hj1 hj2 a ha h
      · omega
  · intro j hj1 hj2
    obtain ⟨_, _, _, _, _, _, _, hDisjLastL, hDisjLastG⟩ := hGr2 j hj1 hj2
    have hcG : s3.mem (A.levelMeta + cfg.P.d + j) = s2.mem (A.levelMeta + cfg.P.d + j) := by
      rw [Nat.add_assoc]; exact hMC _ (by omega)
    have hcL : s3.mem (A.levelMeta + j) = s2.mem (A.levelMeta + j) := hMC _ (by omega)
    rw [hcL, hcG, hHC _ le_rfl, ← E.prec]
    exact ⟨hDisjLastL, hDisjLastG⟩
  · have hSum : (Finset.Ico i₀ cfg.P.d).sum
        (fun j => Rcore.phi (s3.mem (A.handleBase + j)) (coreTok3 j) s3.mem) =
        (Finset.Ico i₀ cfg.P.d).sum
          (fun j => Rcore.phi (s2.mem (A.handleBase + j)) (coreTok3 j) s3.mem) :=
      Finset.sum_congr rfl (fun j hj => by rw [hHC j (by have := Finset.mem_Ico.mp hj; omega)])
    have hc3' : c3 + (Finset.Ico i₀ cfg.P.d).sum
          (fun j => Rcore.phi (s2.mem (A.handleBase + j)) (coreTok3 j) s3.mem) ≤
        (cfg.P.d - i₀) * (Psc.readout + 48) + 50 + (Finset.Ico i₀ cfg.P.d).sum
          (fun j => Rcore.phi (s2.mem (A.handleBase + j)) (coreTok2 j) s2.mem) := hc3
    rw [hSum]
    omega

end MinCostFlow.MinRatio
