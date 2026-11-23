module

public import MinCostFlow.MinRatio.WireChainCoreBranchBIntPrepKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBLoopInvKFBL
public import MinCostFlow.MinRatio.WireShiftDeepCollectKFBL
public import MinCostFlow.MinRatio.WireStmtNoWriteIn
import WordRAM.Tactic

/-!
# The first part of the interior step after the Branch B loop (`WireChainCoreBranchBIntOldKFBL`)

When the plain-step loop of Branch B exits at a level `i₀` with `0 < i₀ < d`, the levels from
`i₀` on are rebuilt. The tree sync after the rebuild needs the old active forests of these
levels. Their cores are still in their start state `ch0`, and op `2` reads them before anything
else changes. So the interior step starts with the collection of the old forests of the cores
`i₀, …, d - 1` into the array `oldPtrs` (index `j` for level `j`, since `reg 71 = 0`). Then it
runs the first part of the rebuild (`wireBranchBIntPrepKFBL`): the batch of level `i₀` is applied
to its graph, op `5` reads the order list of level `i₀ - 1`, and the rebuild counter of level `i₀`
grows by one. The collection must come first, because op `2` on core `i₀` reads the old graph of
level `i₀`, which the batch then changes in place.

* `sparseCoreReadoutFootAt_graph`: the layout contract of the read ops does not depend on the
  start graph of the core.
* `BranchBIntMidKFBL`: the facts at the state after this part.
* `wireBranchBIntOldKFBL_runs`: the run of this part from the exit of the loop, and its cost
  against the sum of the core potentials.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- The first part of the interior step: collect the old forests of the levels from `i₀ = reg 96`
on into `oldPtrs` (`reg 80`), then apply the batch of level `i₀`, read the order list of level
`i₀ - 1`, and count the rebuild. -/
@[expose] def wireBranchBIntOldKFBL (dgApply readOrd readLSF : ℕ) : Stmt :=
  .assign 20 (.reg 96) ;; collectLSFForestsLoop readLSF 80 ;;
  wireBranchBIntPrepKFBL dgApply readOrd

theorem wireBranchBIntOldKFBL_noRand (dgApply readOrd readLSF : ℕ) :
    (wireBranchBIntOldKFBL dgApply readOrd readLSF).NoRand := by
  simp [wireBranchBIntOldKFBL, collectLSFForestsLoop_noRand, wireBranchBIntPrepKFBL_noRand,
    Stmt.NoRand]

/-- The layout contract of the read ops `2` to `5` does not depend on the start graph. -/
theorem sparseCoreReadoutFootAt_graph {w L depth k M N vCap eCap capExp : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G G' : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ}
    (h : SparseCoreReadoutFootAt fmt L depth tool G k M N vCap eCap capExp P allocation R p op) :
    SparseCoreReadoutFootAt fmt L depth tool G' k M N vCap eCap capExp P allocation R p op :=
  ⟨h.op2_runs, h.op3_runs, h.op4_runs, h.op5_runs⟩

/-- Split a sum over the levels `j < d` at the level `m` and at `m + 1`. -/
theorem sum_range_split3 (f : ℕ → ℕ) {m d : ℕ} (h : m + 1 ≤ d) :
    (Finset.range d).sum f = (Finset.range m).sum f + f m + (Finset.Ico (m + 1) d).sum f := by
  rw [← Finset.sum_range_add_sum_Ico f h, Finset.sum_range_succ]

/-- The facts at the state `s` after `wireBranchBIntOldKFBL`, from the exit state `sE` of the loop
at the level `i₀`. The core of level `j` has the token `tokM j`: the cores of the levels `j ≥ i₀`
are in their start state `ch0` and the others in the state `ch` of the loop. Each new footprint
lies in the old one and in the fresh heap `[sE.regs 4, s.regs 4)`. The old forests of the levels
`j ≥ i₀` are at `mem (oldPtrs + j)`, in the footprints of their cores. The order list of the
level `i₀ - 1` is at `ordPtr`, the graph of the level `i₀` now carries the batch, and the
rebuild counter of the level `i₀` grew by one. Below `sE.regs 4` nothing else changed. -/
structure BranchBIntMidKFBL {w vCap eCap : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (A : BranchBAddrs) (oldPtrs i₀ : ℕ)
    (ch0 ch : ChainState cfg.T cfg.P) (curG : MGraph) (sE s : State) (tok tokM : ℕ → Rcore.τ)
    (ordPtr ordWords : ℕ) : Prop where
  regs : ∀ r, 70 ≤ r → r ≠ 99 → s.regs r = sE.regs r
  r6 : s.regs 6 = A.gPtr0 i₀
  r9 : s.regs 9 = ordPtr
  heapLo : sE.regs 4 < ordPtr
  zero : ZeroFrom s.mem (s.regs 4)
  reps : ∀ j < cfg.P.d,
    Rcore.rep (A.coreH j) (if i₀ ≤ j then chainLevelOrdAbs ch0 j else chainLevelOrdAbs ch j)
      (tokM j) s.mem ∧
    (∀ a, Rcore.foot (A.coreH j) (tokM j) a →
      Rcore.foot (A.coreH j) (tok j) a ∨ (sE.regs 4 ≤ a ∧ a < s.regs 4))
  disj : ∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ ≠ j₂ →
    ∀ a, Rcore.foot (A.coreH j₁) (tokM j₁) a → ¬ Rcore.foot (A.coreH j₂) (tokM j₂) a
  oldF : ∀ j, i₀ ≤ j → j < cfg.P.d → ∃ vc ec,
    DynGraphAt s.mem (s.mem (oldPtrs + j)) vc ec (cfg.T.lsfs (ch0.scState j) (ch0.bran j)).F.F ∧
    s.mem (oldPtrs + j) + dynGraphSize vc ec ≤ s.regs 4 ∧
    ∀ a, s.mem (oldPtrs + j) ≤ a → a < s.mem (oldPtrs + j) + dynGraphSize vc ec →
      Rcore.foot (A.coreH j) (tokM j) a
  ord : OrdListAt s.mem ordPtr (cfg.T.rot (ch.scState (i₀ - 1)) (ch.bran (i₀ - 1))) ordWords ∧
    ordWords ≤ ordRotWords (chainLevelOrdAbs ch (i₀ - 1)) (ch.bran (i₀ - 1)) ∧
    ordPtr + ordWords ≤ s.regs 4 ∧ (∀ j < ordWords, s.mem (ordPtr + j) < 2 ^ w)
  graph : DynGraphAt s.mem (A.gPtr0 i₀) vCap eCap curG
  rc : s.mem (A.rcBase + i₀) = ch.rebuildCount i₀ + 1
  tokEq : ∀ j, j + 1 < i₀ → tokM j = tok j
  frame : ∀ a < sE.regs 4,
    (∀ j, i₀ ≤ j + 1 → j < cfg.P.d → ¬ Rcore.foot (A.coreH j) (tok j) a) →
    (a < A.gPtr0 i₀ ∨ A.gPtr0 i₀ + dynGraphSize vCap eCap ≤ a) → a ≠ A.rcBase + i₀ →
    (a < oldPtrs + i₀ ∨ oldPtrs + cfg.P.d ≤ a) → s.mem a = sE.mem a

set_option maxHeartbeats 1600000 in
/-- **The first part of the interior step, from the exit of the Branch B loop.** The loop exits
at `0 < i₀ < d` with the invariant `I` at the state `sE`. The run starts at `st`, which differs
from `sE` only in `regs 16, 17, 18, 99`. The model facts of the level `i₀` (the batch is valid,
within the caps, and gives `curG`) and of the level `i₀ - 1` (its input facts) come from
`UpdateLoopModelInv` at the exit. The cost is that of the collection, of `dgApply` and of op `5`,
against the sum of the core potentials. -/
theorem wireBranchBIntOldKFBL_runs
    {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy N0 oldPtrs i₀ : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {opCore : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ}
    {ℓ' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ}
    {ch : ChainState cfg.T cfg.P} {curG : MGraph} {curU : List Update}
    {curEditsList : List OrdEdit} {oldOrd : ℕ → List End} {sE st : State}
    {tok : ℕ → Rcore.τ} {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists}
    (E : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore
      p opCore)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hOldLo : A.selBase + 1 + 12 * cfg.P.d ≤ oldPtrs)
    (hOldHi : oldPtrs + (cfg.P.d + 1) ≤ A.heapFloor)
    (hN0 : N0 = cfg.N₀) (hLvlM : ∀ j < cfg.P.d, ch0.lvlM j = levelM cfg.TP cfg.P j)
    (hN00 : ch0.N₀ = N0) (hPos : 0 < i₀) (hLt : i₀ < cfg.P.d)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
      EWc ULc ch0 termTok i₀ ch curG curU curEditsList oldOrd sE tok curBatch curBatchWords
      curEdits curEditsWords levelU levelUS D)
    (hstMem : st.mem = sE.mem)
    (hstRegs : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 99 → st.regs r = sE.regs r)
    (h71 : sE.regs 71 = 0) (h80 : sE.regs 80 = oldPtrs)
    (hIn0 : ∀ j, i₀ ≤ j → j < cfg.P.d →
      SparseCoreOrdInput cfg.T cfg.P.k (ch0.lvlM j) ch0.N₀ (ch0.scState j) (ch0.G j)
        (ch0.levelOrd j) (ch0.updCount j))
    (hValid : (ch.G i₀).BatchIsValid curU) (hCaps : BatchWithinCaps vCap eCap curU)
    (hCurG : curG = (ch.G i₀).applyBatch curU)
    (hCountW : ch.rebuildCount i₀ + 1 < 2 ^ w)
    (hInPrev : SparseCoreOrdInput cfg.T cfg.P.k (ch.lvlM (i₀ - 1)) ch.N₀ (ch.scState (i₀ - 1))
      (ch.G (i₀ - 1)) (ch.levelOrd (i₀ - 1)) (ch.updCount (i₀ - 1)))
    (hRoom : sE.regs 4 + 5 * (cfg.P.d - i₀) +
      (1 + ordRotWords (chainLevelOrdAbs ch (i₀ - 1)) (ch.bran (i₀ - 1))) < 2 ^ w) :
    ∃ (s : State) (cost : ℕ) (tokM : ℕ → Rcore.τ) (ordPtr ordWords : ℕ),
      Runs w p ω (wireBranchBIntOldKFBL dgApply (opCore 5) (opCore 2)) st .normal s cost ∧
      s.regs 4 ≤ sE.regs 4 + 5 * (cfg.P.d - i₀) +
        (1 + ordRotWords (chainLevelOrdAbs ch (i₀ - 1)) (ch.bran (i₀ - 1))) ∧
      BranchBIntMidKFBL (w := w) (vCap := vCap) (eCap := eCap) A oldPtrs i₀ ch0 ch curG sE s tok
        tokM ordPtr ordWords ∧
      cost + branchBPhiSum Rcore A tokM s.mem ≤
        (cfg.P.d - i₀) * (Psc.readout + 48) + 670 * curBatchWords +
          Psc.mul * (ordRotWords (chainLevelOrdAbs ch (i₀ - 1)) (ch.bran (i₀ - 1)) + 1) *
            SparseCore.bundleLogFactor (levelM cfg.TP cfg.P (i₀ - 1)) cfg.N₀ + 111 +
          branchBPhiSum Rcore A tok sE.mem := by
  obtain ⟨hFloor, hr10, _, _, _, _, _, _, hr75, _, hr77, hr78, _, hr83, _, hr86, _, _,
    hr96, _, _, _⟩ := I.regs
  have hN : ch.N₀ = N0 := I.modelFrame.2.2.2.2.2.1
  have hLvlCh : ∀ j < cfg.P.d, ch.lvlM j = levelM cfg.TP cfg.P j := fun j hj => by
    rw [I.modelFrame.2.2.2.2.2.2.1]; exact hLvlM j hj
  have hBran : ch.bran = ch0.bran := I.modelFrame.2.1
  have hHBLt := S.hbLt
  have hBBLt := S.bbLt
  have hMetaLt := S.metaLt
  have hRCLt := S.rcLt
  have hGLt := S.gLt i₀ hLt
  set h0 := sE.regs 4 with hh0
  have hR (r : ℕ) (h16 : r ≠ 16) (h17 : r ≠ 17) (h18 : r ≠ 18) (h99 : r ≠ 99) :
      st.regs r = sE.regs r := hstRegs r h16 h17 h18 h99
  have hst4 : st.regs 4 = h0 := hR 4 (by decide) (by decide) (by decide) (by decide)
  have hm1 : i₀ - 1 < cfg.P.d := by omega
  have hm1ne : i₀ - 1 ≠ i₀ := by omega
  have hFootLoc := I.footLoc
  -- the cores from `i₀` on are in their start state
  have hAbs0 : ∀ j, i₀ ≤ j → j < cfg.P.d →
      Rcore.rep (A.coreH j) (chainLevelOrdAbs ch0 j) (tok j) sE.mem := by
    intro j hj1 hj2
    have hRj := (I.reps j hj2).1
    obtain ⟨hGS, hScS⟩ := I.modelFrame.1 j hj1
    by_cases hji : j = i₀
    · subst hji
      rw [ite_eq_left rfl] at hRj
      have hEq : (⟨ch.scState j, ch.G j, oldOrd, ch.updCount j⟩ : SparseCoreOrdAbs cfg.T) =
          chainLevelOrdAbs ch0 j := by
        rw [hGS, hScS, I.oldOrdEq, I.updFrame j le_rfl]; rfl
      rwa [hEq] at hRj
    · rw [ite_eq_right hji] at hRj
      have hEq : chainLevelOrdAbs ch j = chainLevelOrdAbs ch0 j := by
        unfold chainLevelOrdAbs
        rw [hGS, hScS, I.updFrame j hj1]
        congr 1
        simp only [ChainState.levelOrd, chainLevelOrd, show j ≠ 0 by omega, ↓reduceIte]
        rw [(I.modelFrame.1 (j - 1) (by omega)).2, hBran]
      rwa [hEq] at hRj
  -- Step 1: the old forests of the levels from `i₀` on
  let s0 : State := { st with regs := Function.update st.regs 20 i₀ }
  have r0 : Runs w p ω (.assign 20 (.reg 96)) st .normal s0 2 :=
    runs_assign_iff.mpr ⟨i₀, by
      simp [Expr.eval, hR 96 (by decide) (by decide) (by decide) (by decide), hr96], rfl, rfl,
      rfl⟩
  have hs0 (r : ℕ) (h20 : r ≠ 20) : s0.regs r = st.regs r := Function.update_of_ne h20 _ _
  have hs0E (r : ℕ) (h70 : 70 ≤ r) (h99 : r ≠ 99) : s0.regs r = sE.regs r :=
    (hs0 r (by omega)).trans (hR r (by omega) (by omega) (by omega) h99)
  have hs04 : s0.regs 4 = h0 := (hs0 4 (by decide)).trans hst4
  have hs0m : s0.mem = sE.mem := hstMem
  obtain ⟨s1, c1, tokC, r1, h1lo, h1hi, hz1, hReps1, hDisj1, hForests1, hFr1, hRegs1, hc1⟩ :=
    collectLSFForestsLoopKFBL_runs (w := w) (L := L) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (first := i₀) (baseIdx := 0) (dstReg := 80)
      (dstPtrs := oldPtrs) (handleBase := A.handleBase) (branchBase := A.branchBase)
      (levelMeta := A.levelMeta) (fmt := fmt) (T := cfg.T) (CP := cfg.P) (P := Psc)
      (allocation := alloc) (Rcore := Rcore) (p := p) (op := opCore) (st := s0) (ω := ω)
      ch0 A.coreH tok E.loc (by decide) (Nat.zero_le _) hLt.le (by simp [s0])
      ((hs0E 71 (by decide) (by decide)).trans h71) ((hs0E 75 (by decide) (by decide)).trans hr75)
      ((hs0E 77 (by decide) (by decide)).trans hr77) ((hs0E 78 (by decide) (by decide)).trans hr78)
      ((hs0E 83 (by decide) (by decide)).trans hr83) ((hs0E 80 (by decide) (by decide)).trans h80)
      E.kW E.dW (by have := E.w16; omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hs04]; omega) (by rw [hs04, hs0m]; exact I.zero)
      (fun j _ hj => by
        rw [hLvlM j hj, hN00, hN0]; exact sparseCoreReadoutFootAt_graph (E.footAt j hj))
      (fun j hj1 hj2 => by
        obtain ⟨_, _, c3, c4, c5, c6, c7, _, _, _⟩ := I.cells j hj2
        rw [hs0m, hs04]
        refine ⟨c3, by rw [c4, hBran], by rw [← hBran]; exact c5, c6, hAbs0 j hj1 hj2,
          hIn0 j hj1 hj2, (I.reps j hj2).2, fun r _ hr => ?_, Or.inl (by omega), Or.inl (by omega),
          Or.inl (by omega), fun t _ ht hf => ?_, ?_⟩
        · obtain ⟨_, _, sHB, sM, _, _⟩ := I.static r hr
          exact ⟨(sHB j hj2.le).1, (sHB j hj2.le).2, (sM j hj2).2.2.1⟩
        · rcases hFootLoc j hj2 _ hf with h | h <;> omega
        · rw [c7]
          obtain ⟨hGS, _⟩ := I.modelFrame.1 j hj1
          refine ⟨by rw [← hGS]; exact I.graphs j hj2, by have := S.gLt j hj2; omega,
            fun a ha1 ha2 => ⟨fun r _ hr => (I.static r hr).2.2.2.2.1 j hj2 a ha1 ha2,
              Or.inl (by have := S.gLt j hj2; omega)⟩⟩)
      (fun j₁ j₂ _ h1 _ h2 hne => I.disj j₁ h1 j₂ h2 hne)
  rw [hs04] at h1lo h1hi
  simp only [Nat.sub_zero] at hForests1 hFr1
  have hs1E (r : ℕ) (h70 : 70 ≤ r) (h99 : r ≠ 99) : s1.regs r = sE.regs r :=
    (hRegs1 r (Or.inl h70)).trans (hs0E r h70 h99)
  have hs1r10 : s1.regs 10 = curBatch := by
    rw [runs_regs_of_noWriteIn r1 (collectLSFForestsLoop_noWriteIn _ _) 10 (by decide),
      hs0 10 (by decide), hR 10 (by decide) (by decide) (by decide) (by decide), hr10]
  -- the words that the collection keeps
  have hKeep1 : ∀ z < h0, (∀ j, i₀ ≤ j → j < cfg.P.d → ¬ Rcore.foot (A.coreH j) (tok j) z) →
      (z < oldPtrs + i₀ ∨ oldPtrs + cfg.P.d ≤ z) → s1.mem z = sE.mem z := fun z hz hn ho => by
    rw [← hs0m]; exact hFr1 z (by rw [hs04]; exact hz) hn ho
  have hKeep1Low : ∀ j < cfg.P.d, j < i₀ → ∀ z, Rcore.foot (A.coreH j) (tok j) z →
      s1.mem z = sE.mem z := fun j hj hji z hz => by
    refine hKeep1 z ((I.reps j hj).2 z hz) (fun r hr1 hr2 => I.disj j hj r hr2 (by omega) z hz) ?_
    rcases hFootLoc j hj z hz with h | h <;> omega
  -- the cell facts at `s1`
  obtain ⟨_, _, c3p, c4p, c5p, c6p, _, _, _, c10p⟩ := I.cells (i₀ - 1) hm1
  obtain ⟨_, _, _, _, _, _, c7i, _, _, c10i⟩ := I.cells i₀ hLt
  have hStaticOff : ∀ z, BranchBStaticWord cfg.P.d A z →
      (∀ j, i₀ ≤ j → j < cfg.P.d → ¬ Rcore.foot (A.coreH j) (tok j) z) := fun z hz j _ hj =>
    (branchBStaticWord_off S I.static hz).2.1 j hj
  have hStatLt : ∀ z, BranchBStaticWord cfg.P.d A z → z < A.selBase := fun z hz =>
    (branchBStaticWord_off S I.static hz).1
  have hKeepStat : ∀ z, BranchBStaticWord cfg.P.d A z → s1.mem z = sE.mem z := fun z hz =>
    hKeep1 z (by have := hStatLt z hz; omega) (hStaticOff z hz)
      (Or.inl (by have := hStatLt z hz; omega))
  have hSW_g : BranchBStaticWord cfg.P.d A (A.levelMeta + cfg.P.d + i₀) := by
    unfold BranchBStaticWord; omega
  have hSW_h : BranchBStaticWord cfg.P.d A (A.handleBase + (i₀ - 1)) := by
    unfold BranchBStaticWord; omega
  have hSW_b : BranchBStaticWord cfg.P.d A (A.branchBase + (i₀ - 1)) := by
    unfold BranchBStaticWord; omega
  have hSW_rc : BranchBStaticWord cfg.P.d A (A.rcBase + i₀) := by
    unfold BranchBStaticWord; omega
  -- the batch and the graph of the level `i₀` at `s1`
  obtain ⟨hSB, _, hBWords, hBLo, hBHi, _⟩ := I.batch hLt
  have hBatchKeep : ∀ t < curBatchWords, s1.mem (curBatch + t) = sE.mem (curBatch + t) :=
    fun t ht => hKeep1 _ (by omega) (fun j _ hj => (hBWords t ht).2 j hj) (Or.inr (by omega))
  have hGKeep : ∀ z, A.gPtr0 i₀ ≤ z → z < A.gPtr0 i₀ + dynGraphSize vCap eCap →
      s1.mem z = sE.mem z := fun z hz1 hz2 =>
    hKeep1 z (by omega) (fun j _ hj => (I.static j hj).2.2.2.2.1 i₀ hLt z hz1 hz2)
      (Or.inl (by omega))
  have hRepPrev1 : Rcore.rep (A.coreH (i₀ - 1)) (chainLevelOrdAbs ch (i₀ - 1)) (tok (i₀ - 1))
      s1.mem := by
    have hRp := (I.reps (i₀ - 1) hm1).1
    rw [ite_eq_right hm1ne] at hRp
    exact (E.loc _ _ _ _ _ (fun a ha => (hKeep1Low (i₀ - 1) hm1 (by omega) a ha).symm)).1 hRp
  -- Step 2: the batch, op `5` on core `i₀ - 1` and the rebuild counter
  have hs14 : h0 ≤ s1.regs 4 := h1lo
  obtain ⟨_, _, sHBp, sMp, sGp, _⟩ := I.static (i₀ - 1) hm1
  obtain ⟨s2, cost2, h1', words, y, r2, hcurle, hh1le, h24, h29, _, _, _, h26, h2regs, hRepY,
      hFootY, hz2, hOrd2, hWordsLe, hOrdEnd, hOrdW, hG2, hRC2, hFr2, hc2⟩ :=
    wireBranchBIntPrepKFBL_runs (dgApply := dgApply) (d := cfg.P.d) (idx := i₀)
      (curHeap := s1.regs 4) (curBatch := curBatch) (bW := curBatchWords)
      (gPtr := A.gPtr0 i₀) (handleBase := A.handleBase) (branchBase := A.branchBase)
      (levelMeta := A.levelMeta) (rcBase := A.rcBase) (coreH := A.coreH (i₀ - 1))
      (branch := ch.bran (i₀ - 1)) (count := ch.rebuildCount i₀) (G := ch.G i₀) (U := curU)
      (a := chainLevelOrdAbs ch (i₀ - 1)) (x := tok (i₀ - 1)) (st := s1) (ω := ω)
      E.loc (E.footAt (i₀ - 1) hm1) (E.dgApplyC (ch.G i₀) curU curBatchWords)
      ⟨rfl, hs1r10, (hs1E 75 (by decide) (by decide)).trans hr75,
        (hs1E 77 (by decide) (by decide)).trans hr77, (hs1E 78 (by decide) (by decide)).trans hr78,
        (hs1E 83 (by decide) (by decide)).trans hr83, (hs1E 86 (by decide) (by decide)).trans hr86,
        (hRegs1 96 (Or.inl (by decide))).trans ((hs0E 96 (by decide) (by decide)).trans hr96)⟩
      ⟨(hKeepStat _ hSW_g).trans c7i, (hKeepStat _ hSW_h).trans c3p,
        (hKeepStat _ hSW_b).trans c4p, (hKeepStat _ hSW_rc).trans c10i⟩
      hPos ⟨by omega, by omega, by omega, by omega⟩ hCountW E.w16 (by omega) (by omega)
      (fun t ht => Or.inr (by omega))
      (fun t ht => by rw [hBatchKeep t ht]; exact (hBWords t ht).1)
      (batchAt_of_agree' hSB.1 (fun t ht => hBatchKeep t ht)) hValid hCaps
      (dynGraphAt_of_agree (I.graphs i₀ hLt) hGKeep)
      (fun z hz1 hz2 => by
        obtain ⟨_, _, g3, g4, _, _, g7, _, _⟩ := S.gSep i₀ hLt z hz1 hz2
        exact ⟨sGp i₀ hLt z hz1 hz2, by omega, by omega, by omega⟩)
      c5p E.kW c6p hRepPrev1
      (by rw [hLvlCh (i₀ - 1) hm1, hN, hN0] at hInPrev; exact hInPrev)
      (fun z hz => by have := (I.reps (i₀ - 1) hm1).2 z hz; omega)
      hz1 (by omega) (by omega) (sMp i₀ hLt).2.2.2.2
  -- the tokens after the part
  let tokM : ℕ → Rcore.τ := fun j => if j = i₀ - 1 then y else if i₀ ≤ j then tokC j else tok j
  have htokY : tokM (i₀ - 1) = y := ite_eq_left rfl
  have htokC : ∀ j, i₀ ≤ j → tokM j = tokC j := fun j hj => by
    simp only [tokM]; rw [ite_eq_right (show j ≠ i₀ - 1 by omega), ite_eq_left hj]
  have htokL : ∀ j, j < i₀ - 1 → tokM j = tok j := fun j hj => by
    simp only [tokM]
    rw [ite_eq_right (show j ≠ i₀ - 1 by omega), ite_eq_right (show ¬ i₀ ≤ j by omega)]
  have hFootC : ∀ j, i₀ ≤ j → j < cfg.P.d → ∀ a, Rcore.foot (A.coreH j) (tokC j) a →
      Rcore.foot (A.coreH j) (tok j) a ∨ (h0 ≤ a ∧ a < s1.regs 4) := fun j hj1 hj2 a ha => by
    have := (hReps1 j hj1 hj2).2 a ha; rwa [hs04] at this
  -- the words that the second part keeps
  have hKeepC : ∀ j, i₀ ≤ j → j < cfg.P.d → ∀ z, Rcore.foot (A.coreH j) (tokC j) z →
      s2.mem z = s1.mem z := fun j hj1 hj2 z hz => by
    obtain ⟨_, _, _, sMj, sGj, _⟩ := I.static j hj2
    rcases hFootC j hj1 hj2 z hz with h | ⟨hlo, hhi⟩
    · have hzlt := (I.reps j hj2).2 z h
      refine hFr2 z (by omega) (I.disj j hj2 (i₀ - 1) hm1 (by omega) z h) ?_ ?_
      · by_contra hc; push Not at hc; exact sGj i₀ hLt z hc.1 hc.2 h
      · rintro rfl; exact (sMj i₀ hLt).2.2.2.2 h
    · exact hFr2 z hhi (fun hf => by have := (I.reps (i₀ - 1) hm1).2 z hf; omega)
        (Or.inr (by omega)) (by omega)
  have hKeepLow : ∀ j < cfg.P.d, j ≠ i₀ - 1 → j < i₀ → ∀ z, Rcore.foot (A.coreH j) (tok j) z →
      s2.mem z = sE.mem z := fun j hj hjm hji z hz => by
    obtain ⟨_, _, _, sMj, sGj, _⟩ := I.static j hj
    have hzlt := (I.reps j hj).2 z hz
    rw [hFr2 z (by omega) (I.disj j hj (i₀ - 1) hm1 hjm z hz) ?_ ?_]
    · exact hKeep1Low j hj hji z hz
    · by_contra hc; push Not at hc; exact sGj i₀ hLt z hc.1 hc.2 hz
    · rintro rfl; exact (sMj i₀ hLt).2.2.2.2 hz
  -- the cores after the part
  have hRepsM : ∀ j < cfg.P.d,
      Rcore.rep (A.coreH j)
        (if i₀ ≤ j then chainLevelOrdAbs ch0 j else chainLevelOrdAbs ch j) (tokM j) s2.mem ∧
      (∀ a, Rcore.foot (A.coreH j) (tokM j) a →
        Rcore.foot (A.coreH j) (tok j) a ∨ (h0 ≤ a ∧ a < s2.regs 4)) := by
    intro j hj
    by_cases hjm : j = i₀ - 1
    · subst hjm
      rw [htokY, ite_eq_right (show ¬ i₀ ≤ i₀ - 1 by omega), h24]
      exact ⟨hRepY, fun a ha => (hFootY a ha).imp id fun h => ⟨by omega, by omega⟩⟩
    · by_cases hji : i₀ ≤ j
      · rw [htokC j hji, ite_eq_left hji, h24]
        refine ⟨(E.loc _ _ _ _ _ (fun a ha => (hKeepC j hji hj a ha).symm)).1
          (hReps1 j hji hj).1, fun a ha => ?_⟩
        rcases hFootC j hji hj a ha with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by omega⟩
      · rw [htokL j (by omega), ite_eq_right hji]
        have hRj := (I.reps j hj).1
        rw [ite_eq_right (show j ≠ i₀ by omega)] at hRj
        exact ⟨(E.loc _ _ _ _ _ (fun a ha => (hKeepLow j hj hjm (by omega) a ha).symm)).1 hRj,
          fun a ha => Or.inl ha⟩
  have hFine : ∀ j < cfg.P.d, ∀ a, Rcore.foot (A.coreH j) (tokM j) a →
      Rcore.foot (A.coreH j) (tok j) a ∨ (j = i₀ - 1 ∧ s1.regs 4 ≤ a ∧ a < h1') ∨
        (i₀ ≤ j ∧ h0 ≤ a ∧ a < s1.regs 4) := fun j hj a ha => by
    by_cases hjm : j = i₀ - 1
    · subst hjm; rw [htokY] at ha
      exact (hFootY a ha).imp id fun h => Or.inl ⟨rfl, h⟩
    · by_cases hji : i₀ ≤ j
      · rw [htokC j hji] at ha
        exact (hFootC j hji hj a ha).imp id fun h => Or.inr ⟨hji, h⟩
      · rw [htokL j (by omega)] at ha; exact Or.inl ha
  have hDisjM : ∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ ≠ j₂ → ∀ a,
      Rcore.foot (A.coreH j₁) (tokM j₁) a → ¬ Rcore.foot (A.coreH j₂) (tokM j₂) a := by
    intro j₁ hj₁ j₂ hj₂ hne a ha1 ha2
    rcases hFine j₁ hj₁ a ha1 with h1 | ⟨e1, l1, u1⟩ | ⟨e1, l1, u1⟩ <;>
      rcases hFine j₂ hj₂ a ha2 with h2 | ⟨e2, l2, u2⟩ | ⟨e2, l2, u2⟩
    · exact I.disj j₁ hj₁ j₂ hj₂ hne a h1 h2
    · have := (I.reps j₁ hj₁).2 a h1; omega
    · have := (I.reps j₁ hj₁).2 a h1; omega
    · have := (I.reps j₂ hj₂).2 a h2; omega
    · omega
    · omega
    · have := (I.reps j₂ hj₂).2 a h2; omega
    · omega
    · rw [htokC j₁ e1] at ha1; rw [htokC j₂ e2] at ha2
      exact hDisj1 j₁ j₂ e1 hj₁ e2 hj₂ hne a ha1 ha2
  -- the old forests
  have hOldF : ∀ j, i₀ ≤ j → j < cfg.P.d → ∃ vc ec,
      DynGraphAt s2.mem (s2.mem (oldPtrs + j)) vc ec
        (cfg.T.lsfs (ch0.scState j) (ch0.bran j)).F.F ∧
      s2.mem (oldPtrs + j) + dynGraphSize vc ec ≤ s2.regs 4 ∧
      ∀ a, s2.mem (oldPtrs + j) ≤ a → a < s2.mem (oldPtrs + j) + dynGraphSize vc ec →
        Rcore.foot (A.coreH j) (tokM j) a := by
    intro j hj1 hj2
    obtain ⟨vc, ec, hDG, hEnd, hInF⟩ := hForests1 j hj1 hj2
    have hcell : s2.mem (oldPtrs + j) = s1.mem (oldPtrs + j) :=
      hFr2 _ (by omega)
        (fun hf => by rcases hFootLoc (i₀ - 1) hm1 _ hf with h | h <;> omega)
        (Or.inr (by omega)) (by omega)
    refine ⟨vc, ec, ?_, by rw [hcell, h24]; omega, fun a ha1 ha2 => ?_⟩
    · rw [hcell]
      exact dynGraphAt_of_agree hDG (fun x hx1 hx2 => hKeepC j hj1 hj2 x (hInF x hx1 hx2))
    · rw [htokC j hj1]; rw [hcell] at ha1 ha2; exact hInF a ha1 ha2
  -- the run
  have rAll : Runs w p ω (wireBranchBIntOldKFBL dgApply (opCore 5) (opCore 2)) st .normal s2
      (2 + (c1 + cost2 + 1) + 1) := by
    unfold wireBranchBIntOldKFBL
    exact runs_seq_iff.mpr (Or.inr ⟨s0, 2, c1 + cost2 + 1, r0,
      runs_seq_iff.mpr (Or.inr ⟨s1, c1, cost2, r1, r2, rfl⟩), rfl⟩)
  -- the potentials
  have hPA : (Finset.range (i₀ - 1)).sum (fun j => Rcore.phi (A.coreH j) (tokM j) s2.mem) =
      (Finset.range (i₀ - 1)).sum (fun j => Rcore.phi (A.coreH j) (tok j) sE.mem) :=
    Finset.sum_congr rfl (fun j hj => by
      have hj' := Finset.mem_range.mp hj
      rw [htokL j hj']
      exact (E.loc _ (chainLevelOrdAbs ch j) _ _ _
        (fun a ha => (hKeepLow j (by omega) (by omega) (by omega) a ha).symm)).2.symm)
  have hPC : (Finset.Ico i₀ cfg.P.d).sum (fun j => Rcore.phi (A.coreH j) (tokM j) s2.mem) =
      (Finset.Ico i₀ cfg.P.d).sum (fun j => Rcore.phi (A.coreH j) (tokC j) s1.mem) :=
    Finset.sum_congr rfl (fun j hj => by
      have hj' := Finset.mem_Ico.mp hj
      rw [htokC j hj'.1]
      exact (E.loc _ (chainLevelOrdAbs ch0 j) _ _ _
        (fun a ha => (hKeepC j hj'.1 hj'.2 a ha).symm)).2.symm)
  have hPD : Rcore.phi (A.coreH (i₀ - 1)) (tok (i₀ - 1)) s1.mem =
      Rcore.phi (A.coreH (i₀ - 1)) (tok (i₀ - 1)) sE.mem :=
    (E.loc _ (chainLevelOrdAbs ch (i₀ - 1)) _ _ _
      (fun a ha => hKeep1Low (i₀ - 1) hm1 (by omega) a ha)).2
  have e1 := sum_range_split3 (fun j => Rcore.phi (A.coreH j) (tokM j) s2.mem) (m := i₀ - 1)
    (d := cfg.P.d) (by omega)
  have e2 := sum_range_split3 (fun j => Rcore.phi (A.coreH j) (tok j) sE.mem) (m := i₀ - 1)
    (d := cfg.P.d) (by omega)
  rw [Nat.sub_add_cancel (show 1 ≤ i₀ by omega)] at e1 e2
  rw [htokY] at e1
  rw [hs0m] at hc1
  refine ⟨s2, _, tokM, s1.regs 4 + 1, words, rAll, by omega,
    { regs := fun r h70 h99 => (h2regs r (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)).trans (hs1E r h70 h99)
      r6 := h26
      r9 := h29
      heapLo := by omega
      zero := by rw [h24]; exact hz2
      reps := hRepsM
      disj := hDisjM
      oldF := hOldF
      ord := ⟨hOrd2, hWordsLe, by rw [h24]; omega, hOrdW⟩
      graph := by rw [hCurG]; exact hG2
      rc := hRC2
      tokEq := fun j hj => htokL j (by omega)
      frame := fun a ha hoff hg hrc ho => by
        rw [hFr2 a (by omega) (hoff (i₀ - 1) (by omega) hm1) hg hrc]
        exact hKeep1 a ha (fun j hj1 hj => hoff j (by omega) hj) ho }, ?_⟩
  unfold branchBPhiSum
  rw [e1, e2, hPA, hPC]
  omega

end MinCostFlow.MinRatio

end
