module

public import MinCostFlow.MinRatio.WireChainCoreBranchBForestLocGoalKFBL
import MinCostFlow.MinRatio.WireShiftDeepSpecKFBL
import WordRAM.Tactic

/-!
# Where the forests lie at the interior exit of Branch B (`WireChainCoreBranchBExitLocInt`)

This file proves `BranchBIntExitForestLocGoalKFBL`
(`WireChainCoreBranchBForestLocGoalKFBL.lean`): at every run of the interior exit
`wireBranchBIntKFBL …`, each word of a graph in the old forest list (at `oldPtrs + i₀`) or in the
new forest list (at `newPtrs + i₀`) lies in the footprint of a core `j < d` at the loop-exit
tokens `tok`, in the footprint of the old last level at `termTok`, or in the fresh heap
`[A.heapFloor, out.regs 4)`.

The proof runs the three parts of `wireBranchBIntKFBL` (`wireBranchBIntOldKFBL_runs`,
`wireBranchBIntRebNewKFBL_runs`, `wireBranchBIntTailKFBL_runs`), identifies any run with it by
`Runs.det`, and fixes the graph caps by `dynGraphAt_caps_eq`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

set_option maxHeartbeats 2400000 in
/-- **Proof of `BranchBIntExitForestLocGoalKFBL`.** At every run of the interior exit, the graphs
of the old forests at `oldPtrs + i₀` and of the new forests at `newPtrs + i₀` lie in the footprints
of the cores at `tok`, of the old last level at `termTok`, or in `[A.heapFloor, out.regs 4)`. -/
theorem branchBIntExitForestLocGoalKFBL_proved : BranchBIntExitForestLocGoalKFBL := by
  intro w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
    edgeProc signExt mul intDiv copy N0 oldPtrs newPtrs intCap i₀ wordExp stretchPrec
    capLimit coreLenProc lastInit lastMul lastSpace
    fmt cfg Psc alloc lastAlloc Ginit reembFn Rcore RL p opCore opLast ω A origLen ℓ' g'
    BWc EWc ULc ch0 termTok ch curG curU curEditsList curEnc oldOrd sE st tok
    curBatch curBatchWords curEdits curEditsWords levelU levelUS D levelSpace levelCost
    E S hOldLo hOldNew hNewHi hN0 hLvlM hN00 hPos hLt I hM hFire hstMem hstRegs
    h71 h80 h81 hIn0 hOldLast _ _ next hNext hWordExpEq hInitOrdEq
    hNextN hNextRot hImpl hcapLim hCoreLenProc hLastImpl hLevelSpaceDom hLevelCostDom
    hLastSpaceDom hFCap hLastFCap hLWord hPWord hWidth hDepthW hNW hRoom
    out cost hRun
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
  obtain ⟨_, _, _, _, _, _, hRebW, _, _, _, _, _, _⟩ :=
    branchBIntNext_facts (fmt := fmt) (Psc := Psc) ch curG ℓ' g' curEnc i₀ next hNext hPos hLt
      hReb hWordExpEq E.prec hInitOrdEq hNextN hNextRot
  have hHBLt := S.hbLt
  have hBBLt := S.bbLt
  have hMetaLt := S.metaLt
  have hUCLt := S.ucLt
  have hRCLt := S.rcLt
  have hGLt : A.gPtr0 i₀ + dynGraphSize vCap eCap ≤ A.selBase := S.gLt i₀ hLt
  have hm1 : i₀ - 1 < cfg.P.d := by omega
  have hGLt1 : A.gPtr0 (i₀ - 1) + dynGraphSize vCap eCap ≤ A.selBase := S.gLt (i₀ - 1) hm1
  have hFootLoc := I.footLoc
  have hFootOld := I.footOld
  -- Part 1
  obtain ⟨s, c1, tokM, ordPtr, ordWords, r1, h1hi, M, _⟩ :=
    wireBranchBIntOldKFBL_runs (ω := ω) (st := st) E S hOldLo (by omega) hN0 hLvlM hN00 hPos
      hLt I hstMem hstRegs h71 h80 hIn0 hValid hCaps hCurG hRebW hInPrev (by omega)
  -- Part 2
  obtain ⟨s3, c2, termTokN, coreTok, r2, h3hi, B, _⟩ :=
    wireBranchBIntRebNewKFBL_runs (ω := ω) E S hOldLo (by omega) (by omega) hNewHi hPos hLt I M
      h71 h81 next hNext hReb hWordExpEq hInitOrdEq hNextN hNextRot hImpl hcapLim hCoreLenProc
      hLastImpl hLevelSpaceDom hLevelCostDom hLastSpaceDom hFCap hLastFCap hLWord hPWord hWidth
      hDepthW hNW (by omega)
  have hsE4 : sE.regs 4 < s.regs 4 := by have := M.heapLo; have := M.ord.2.2.1; omega
  have hs3 : s.regs 4 ≤ s3.regs 4 := B.heapLo
  have hRoom3 : s3.regs 4 + 7 < 2 ^ w := by omega
  clear hRoom h1hi h3hi
  have hR3 (r : ℕ) (h70 : 70 ≤ r) (h99 : r ≠ 99) : s3.regs r = sE.regs r :=
    (B.regs r h70).trans (M.regs r h70 h99)
  have hTokM1 : ∀ a, Rcore.foot (A.coreH (i₀ - 1)) (tokM (i₀ - 1)) a →
      Rcore.foot (A.coreH (i₀ - 1)) (tok (i₀ - 1)) a ∨ (sE.regs 4 ≤ a ∧ a < s.regs 4) :=
    (M.reps (i₀ - 1) hm1).2
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
  have h3HB : ∀ j < i₀, s3.mem (A.handleBase + j) = sE.mem (A.handleBase + j) := fun j hj =>
    hK3S _ (.hb (by omega) (by omega)) (.hb S hj hLt)
  have h3BB : ∀ j < i₀, s3.mem (A.branchBase + j) = sE.mem (A.branchBase + j) := fun j hj =>
    hK3S _ (.bb (by omega) (by omega)) (.bb S hj hLt)
  have h3LMd : ∀ j ≤ i₀, s3.mem (A.levelMeta + cfg.P.d + j) =
      sE.mem (A.levelMeta + cfg.P.d + j) := fun j hj =>
    hK3S _ (.lm (by omega) (by omega)) (.lmd S hj hLt)
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
  obtain ⟨out', c3, _, _, r3, _, _, hout4, _, _, _, _, _, _, _, hFrT, _, _, _, _, _, _⟩ :=
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
  have hRuns' : Runs w p ω (wireBranchBIntKFBL dgApply initCore (opCore 3) (opCore 2) coreLenProc
      (opCore 5) lastInit) st .normal out' (c1 + (c2 + c3 + 1) + 1) := by
    unfold wireBranchBIntKFBL
    exact runs_seq_iff.mpr (Or.inr ⟨s, c1, c2 + c3 + 1, r1,
      runs_seq_iff.mpr (Or.inr ⟨s3, c2, c3, r2, r3, rfl⟩), rfl⟩)
  obtain ⟨_, rfl, _⟩ := Runs.det hRuns' hRun
  have hKeepHigh : ∀ a, s.regs 4 ≤ a → a < s3.regs 4 → out'.mem a = s3.mem a := fun a h1 h2 =>
    hFrT a h2 (fun hf => by
      rcases hTokM1 a hf with h | h
      · have := (I.reps (i₀ - 1) hm1).2 a h; omega
      · omega) (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have hKeepMid : ∀ a, A.selBase + 1 + 12 * cfg.P.d ≤ a → a < A.heapFloor →
      out'.mem a = s3.mem a := fun a h1 h2 =>
    hFrT a (by omega) (fun hf => by
      rcases hTokM1 a hf with h | h
      · rcases hFootLoc (i₀ - 1) hm1 a h with h' | h' <;> omega
      · omega) (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have hKeepAll : ∀ a < sE.regs 4,
      (∀ j, i₀ ≤ j + 1 → j < cfg.P.d → ¬ Rcore.foot (A.coreH j) (tok j) a) →
      (a < A.gPtr0 i₀ ∨ A.gPtr0 i₀ + dynGraphSize vCap eCap ≤ a) →
      BranchBIntKeepCell cfg.P.d i₀ A a →
      (a < A.ucBase + i₀ ∨ A.ucBase + cfg.P.d ≤ a) →
      a < A.selBase → out'.mem a = sE.mem a := fun a ha hc hg hk hu hlt => by
    have hnf : ¬ Rcore.foot (A.coreH (i₀ - 1)) (tokM (i₀ - 1)) a := fun hf => by
      rcases hTokM1 a hf with h | h
      · exact hc (i₀ - 1) (by omega) hm1 h
      · omega
    rw [← hKeep3 a ha hc hg hk (Or.inl (by omega)) (Or.inl (by omega))]
    exact hFrT a (by omega) hnf hu (by omega) (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · intro t ht vc ec hDG x hx1 hx2
    have ht' := ht
    rw [chainSuffixForests_length] at ht'
    by_cases htLt : t < cfg.P.d - i₀
    · obtain ⟨vc0, ec0, hDG0, _, hFt⟩ := M.oldF (i₀ + t) (by omega) (by omega)
      have hSub : oldPtrs + i₀ + t = oldPtrs + (i₀ + t) := by omega
      have hPtr : out'.mem (oldPtrs + (i₀ + t)) = s.mem (oldPtrs + (i₀ + t)) :=
        (hKeepMid _ (by omega) (by omega)).trans
          (B.frame _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
            ⟨Or.inr (by omega), Or.inr (by omega)⟩ (Or.inl (by omega)))
      have hDG0' : DynGraphAt out'.mem (out'.mem (oldPtrs + i₀ + t)) vc0 ec0
          (cfg.T.lsfs (ch0.scState (i₀ + t)) (ch0.bran (i₀ + t))).F.F := by
        rw [hSub, hPtr]
        refine dynGraphAt_of_agree hDG0 (fun y hy1 hy2 => ?_)
        have hf := hFt y hy1 hy2
        have hnf : ¬ Rcore.foot (A.coreH (i₀ - 1)) (tokM (i₀ - 1)) y :=
          M.disj (i₀ + t) (by omega) (i₀ - 1) hm1 (by omega) y hf
        rcases (M.reps (i₀ + t) (by omega)).2 y hf with h0 | ⟨_, h2⟩
        · have hsel := hFootOld (i₀ + t) (by omega) (by omega) y h0
          obtain ⟨f1, f2, f3, f4, f5, _⟩ :=
            branchBCoresDisjStatic_footSep I.static (r := i₀ + t) (by omega) h0
          have hk : BranchBIntKeepCell cfg.P.d i₀ A y := .of_sep f1 f2 f3 f5 hLt
          exact (hFrT y (by omega) hnf (f4.imp_left (fun h => by omega)) (by omega) (by omega)
            (by omega)).trans (B.frame y (by omega) hk.2.1 hk.2.2.1 hk.2.2.2 (Or.inl (by omega)))
        · exact (hFrT y (by omega) hnf (Or.inr (by omega)) (by omega) (by omega) (by omega)).trans
            (B.frame y h2 (Or.inr (by omega)) (Or.inr (by omega))
              ⟨Or.inr (by omega), Or.inr (by omega)⟩ (Or.inr (by omega)))
      rw [chainSuffixForests_getElem_lt ch0 htLt] at hDG
      obtain ⟨hvc, hec⟩ := dynGraphAt_caps_eq hDG hDG0'
      subst hvc hec
      rw [hSub, hPtr] at hx1 hx2
      rcases (M.reps (i₀ + t) (by omega)).2 x (hFt x hx1 hx2) with h0 | ⟨h1, h2⟩
      · exact Or.inl ⟨i₀ + t, by omega, h0⟩
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · have htEq : t = cfg.P.d - i₀ := by omega
      subst htEq
      obtain ⟨vc0, ec0, hDG0, hFt⟩ := hOldLast
      have hSub : oldPtrs + i₀ + (cfg.P.d - i₀) = oldPtrs + cfg.P.d := by omega
      have hPtr : out'.mem (oldPtrs + cfg.P.d) = sE.mem (oldPtrs + cfg.P.d) :=
        (hKeepMid _ (by omega) (by omega)).trans
          ((B.frame _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
            ⟨Or.inr (by omega), Or.inr (by omega)⟩ (Or.inl (by omega))).trans
            (M.frame _ (by omega)
              (fun j _ hj hf => by rcases hFootLoc j hj _ hf with h | h <;> omega)
              (Or.inr (by omega)) (by omega) (Or.inr (by omega))))
      have hDG0' : DynGraphAt out'.mem (out'.mem (oldPtrs + i₀ + (cfg.P.d - i₀))) vc0 ec0
          (ch0.lastLSFs ch0.lastBran).F.F := by
        rw [hSub, hPtr]
        refine dynGraphAt_of_agree hDG0 (fun y hy1 hy2 => ?_)
        obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := I.term.2 y (hFt y hy1 hy2)
        exact hKeepAll y (by omega) (fun j _ hj => t2 j hj) (t3 i₀ hLt).1
          (.of_sep t4 t5 t6 (t8.imp_right Nat.le_of_lt) hLt) (t7.imp_left (fun h => by omega)) t1
      rw [chainSuffixForests_getElem_last] at hDG
      obtain ⟨hvc, hec⟩ := dynGraphAt_caps_eq hDG hDG0'
      subst hvc hec
      rw [hSub, hPtr] at hx1 hx2
      exact Or.inr (Or.inl (hFt x hx1 hx2))
  · intro t ht vc ec hDG x hx1 hx2
    have hNewFOut : ForestPtrListAt out'.mem (newPtrs + i₀) (chainSuffixForests next i₀) intCap
        (out'.regs 4) :=
      B.newF.congr_from B.newFLo (fun k hk => by
          rw [chainSuffixForests_length] at hk
          exact hKeepMid _ (by omega) (by omega))
        (fun a h1 h2 => hKeepHigh a h1 h2) (by omega)
    obtain ⟨vc0, ec0, hDG0, hEnd0, _⟩ := hNewFOut.2 t ht
    obtain ⟨hvc, hec⟩ := dynGraphAt_caps_eq hDG hDG0
    subst hvc hec
    have hPtr : out'.mem (newPtrs + i₀ + t) = s3.mem (newPtrs + i₀ + t) := by
      have ht' := ht
      rw [chainSuffixForests_length] at ht'
      exact hKeepMid _ (by omega) (by omega)
    have hLo : s.regs 4 ≤ s3.mem (newPtrs + i₀ + t) := B.newFLo t ht
    exact Or.inr (Or.inr ⟨by omega, by omega⟩)

end MinCostFlow.MinRatio
