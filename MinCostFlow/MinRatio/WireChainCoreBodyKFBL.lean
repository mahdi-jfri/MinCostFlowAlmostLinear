module

public import MinCostFlow.MinRatio.WireChainCoreInitKFBL
import WordRAM.Tactic

/-!
# The chain core: Phase 0 and the rebuild test (`WireChainCoreBodyKFBL`)

The chain core `ordChainUpdateCoreBodyKFBL branchA branchB` first runs Phase 0
(`updateCoreInitRegsKFBL`), which loads the solver header into the high registers and reserves
`1 + 12 d` words for the select slots and the `3 (d + 1) + 4` words of the forest lists. Then it
tests whether level `0` must be rebuilt: it loads the length of the batch at `uIntBuf`, the
update counter of level `0` and the rebuild threshold of level `0`, and compares. If the
threshold is below the sum, it runs Branch A (every level is rebuilt). Otherwise it runs Branch B
(the levels take plain steps until one must be rebuilt).

`ordChainUpdateCoreBodyKFBL_dispatch` gives the state after the test, with all the registers
that the two branches read, from the premises of `OrdChainUpdateCoreSpecWExtKFBL`. Both branches
use it.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The chain core: Phase 0, the rebuild test at level `0`, then `branchA` when the test fires
and `branchB` when it does not. The test reads the batch length `mem uIntBuf` (`reg 87`), the
update counter `mem updCountBase` (`reg 85`) and the threshold `mem table` (`reg 74`). -/
@[expose] def ordChainUpdateCoreBodyKFBL (branchA branchB : Stmt) : Stmt :=
  updateCoreInitRegsKFBL ;;
  .assign 16 (.load (.reg 87)) ;;
  .assign 17 (.load (.reg 85)) ;;
  .assign 18 (.load (.reg 74)) ;;
  .cond (.bin .lt (.reg 18) (.bin .add (.reg 17) (.reg 16))) branchA branchB

theorem ordChainUpdateCoreBodyKFBL_noRand {branchA branchB : Stmt} (hA : branchA.NoRand)
    (hB : branchB.NoRand) : (ordChainUpdateCoreBodyKFBL branchA branchB).NoRand := by
  simp [ordChainUpdateCoreBodyKFBL, Stmt.NoRand, updateCoreInitRegsKFBL_noRand, hA, hB]

/-- Phase 0 and the rebuild test of the chain core, from the premises of
`OrdChainUpdateCoreSpecWExtKFBL`. The state `st` after the test has the memory `mem` and the
registers that both branches read. A run of `branchA` from `st` when the test fires, or of
`branchB` when it does not, gives a run of the whole core from the start state, at `c0 ≤ 210`
more steps. -/
theorem ordChainUpdateCoreBodyKFBL_dispatch
    {w L P m V psi k epsExp drainUnit root uIntBuf editsPtr editWords g l heap pos bW : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {ω : ℕ → Bool}
    {mem0 mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {U : List Update} {branchA branchB : Stmt}
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hMemEq : ∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hSmallMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2 bW)
    (hdPos : 0 < cfg.P.d) (hw18 : 18 < 2 ^ w) (hULeHeap : uIntBuf ≤ heap)
    (hHeapW : heap + (1 + 12 * cfg.P.d) + 3 * (cfg.P.d + 1) + 4 < 2 ^ w)
    (hSumW :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      model.chain.updCount 0 + tr.2.2.2.2.length < 2 ^ w) :
    let d := cfg.P.d
    let cnt := d + 1
    let arrBase := heap + 1 + 12 * d
    let handleBase := tok.handle + 18
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    ∃ (st : State) (c0 : ℕ), st.mem = mem ∧ c0 ≤ 210 ∧
      (st.regs 4 = arrBase + 3 * cnt + 4 ∧ st.regs 70 = root ∧ st.regs 71 = 0 ∧
        st.regs 72 = heap ∧ st.regs 73 = tok.handle ∧ st.regs 75 = d ∧ st.regs 76 = cfg.P.k ∧
        st.regs 77 = handleBase ∧ st.regs 78 = handleBase + cnt ∧ st.regs 79 = cnt ∧
        st.regs 80 = arrBase ∧ st.regs 81 = arrBase + cnt ∧
        st.regs 82 = solverLvlMAddr tok.table d ∧ st.regs 83 = solverLevelMetaAddr tok.table d ∧
        st.regs 85 = tok.levelsEnd + 3 * cnt ∧ st.regs 86 = tok.levelsEnd + 2 * cnt ∧
        st.regs 87 = uIntBuf ∧ st.regs 90 = g ∧ st.regs 91 = l ∧
        st.regs 92 = arrBase + 2 * cnt ∧ st.regs 93 = arrBase + 3 * cnt ∧
        st.regs 94 = L ∧ st.regs 95 = P ∧ st.regs 98 = Expander.chosenL (cfg.P.M₀ ^ 2)) ∧
      (st.regs 74 = tok.table ∧ st.regs 84 = tok.levelsEnd ∧ st.regs 88 = editsPtr ∧
        st.regs 89 = editWords) ∧
      ∀ (o : Outcome) (out : State) (c : ℕ),
        (intRebuildThreshold cfg.P cfg.N₀ 0 < model.chain.updCount 0 + tr.2.2.2.2.length →
          Runs w p ω branchA st o out c →
          Runs w p ω (ordChainUpdateCoreBodyKFBL branchA branchB)
            (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos) o out
            (c0 + c)) ∧
        (¬ intRebuildThreshold cfg.P cfg.N₀ 0 < model.chain.updCount 0 + tr.2.2.2.2.length →
          Runs w p ω branchB st o out c →
          Runs w p ω (ordChainUpdateCoreBodyKFBL branchA branchB)
            (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos) o out
            (c0 + c)) := by
  dsimp only
  obtain ⟨hRootDir0, _, hNumHdr0, hChainHdr0, _, _, _, _, hSched0, _, _, _, _, _, _, _, _, _,
    hWire0, hTags0⟩ := hRep0
  obtain ⟨hOwn, hT1, hT2, hT3, hT4, hT5, _⟩ := hTags0
  have hMemTag {a v : ℕ} (ht : tok.tag a = v) (h0 : v ≠ 0) (h6 : v ≠ 6) (h7 : v ≠ 7)
      (h8 : v ≠ 8) : mem a = mem0 a ∧ a < uIntBuf := by
    have hlt : a < uIntBuf := hFootLt a (Or.inl (hOwn a (by omega)))
    exact ⟨hMemEq a hlt (by omega) (by omega) (by omega), hlt⟩
  -- the words that Phase 0 reads
  have hR0 := hMemTag (hT1 0 (by omega)) (by decide) (by decide) (by decide) (by decide)
  have hR1 := hMemTag (hT1 1 (by omega)) (by decide) (by decide) (by decide) (by decide)
  have hR2 := hMemTag (hT1 2 (by omega)) (by decide) (by decide) (by decide) (by decide)
  have hH5 := hMemTag (hT2 5 (by omega)) (by decide) (by decide) (by decide) (by decide)
  have hH8 := hMemTag (hT2 8 (by omega)) (by decide) (by decide) (by decide) (by decide)
  have hH11 := hMemTag (hT2 11 (by omega)) (by decide) (by decide) (by decide) (by decide)
  have hH12 := hMemTag (hT2 12 (by omega)) (by decide) (by decide) (by decide) (by decide)
  have hH17 := hMemTag (hT2 17 (by omega)) (by decide) (by decide) (by decide) (by decide)
  have hLT := hMemTag (hT4 (cfg.P.d + 1) (by omega)) (by decide) (by decide) (by decide)
    (by decide)
  have hUC := hMemTag (hT5 (3 * (cfg.P.d + 1)) (by omega)) (by decide) (by decide) (by decide)
    (by decide)
  have hTab := hMemTag (hT3 0 (by omega)) (by decide) (by decide) (by decide) (by decide)
  have hLM := hMemTag (hMeta0.2.2.2.2.1 0 (by omega)) (by omega) (by omega) (by omega)
    (by omega)
  have hRoot0 : mem root = tok.handle := by
    rw [← add_zero root, hR0.1]; simpa using hRootDir0 0 (by simp)
  have hRoot1 : mem (root + 1) = tok.table := by rw [hR1.1]; simpa using hRootDir0 1 (by simp)
  have hRoot2 : mem (root + 2) = tok.levelsEnd := by
    rw [hR2.1]; simpa using hRootDir0 2 (by simp)
  have hL : mem (tok.handle + 5) = L := by rw [hH5.1]; simpa using hNumHdr0 0 (by simp)
  have hP : mem (tok.handle + 8) = P := by
    rw [hH8.1, show tok.handle + 8 = tok.handle + 5 + 3 by omega]
    simpa using hNumHdr0 3 (by simp)
  have hD : mem (tok.handle + 11) = cfg.P.d := by
    rw [hH11.1, show tok.handle + 11 = tok.handle + 9 + 2 by omega]
    simpa using hChainHdr0 2 (by simp)
  have hK : mem (tok.handle + 12) = cfg.P.k := by
    rw [hH12.1, show tok.handle + 12 = tok.handle + 9 + 3 by omega]
    simpa using hChainHdr0 3 (by simp)
  have hDepth : mem (tok.handle + 17) = Expander.chosenL (cfg.P.M₀ ^ 2) := by
    rw [hH17.1, show tok.handle + 17 = tok.handle + 9 + 8 by omega]
    simpa using hChainHdr0 8 (by simp)
  have hLenW : mem uIntBuf =
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2.length :=
    hSmallMem.1.2.1
  have hUCW : mem (tok.levelsEnd + 3 * (cfg.P.d + 1)) = model.chain.updCount 0 := by
    rw [hUC.1]; simpa using hSched0.2.2.2.1 0 (by omega)
  have hTabW : mem tok.table = intRebuildThreshold cfg.P cfg.N₀ 0 := by
    rw [← add_zero tok.table, hTab.1]; exact hWire0.1 0 (by omega)
  -- Phase 0
  obtain ⟨s0, cI, rI, hcI, hs0Mem, hr70, hr71, hr72, hr73, hr74, hr75, hr76, hr77, hr78, hr79,
    hr80, hr81, hr82, hr83, hr84, hr85, hr86, hr87, hr88, hr89, hr90, hr91, hr92, hr93, hr94,
    hr95, hr98, hr4⟩ :=
    updateCoreInitRegsKFBL_runs (p := p) (ω := ω) (editsPtr := editsPtr) (editWords := editWords)
      (g := g) (l := l) (heap := heap) (uIntBuf := uIntBuf) (pos := pos) hRoot0 hRoot1 hRoot2 hL
      hP hD hK hDepth (by have := hR2.2; omega) (by have := hLT.2; omega)
      (by have := hLM.2; omega)
      (by have := hUC.2; omega) hHeapW hw18
  -- the test
  let len :=
    (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2.length
  let uc := model.chain.updCount 0
  let thr := intRebuildThreshold cfg.P cfg.N₀ 0
  let sa : State := { s0 with regs := Function.update s0.regs 16 len }
  let sb : State := { sa with regs := Function.update sa.regs 17 uc }
  let sc : State := { sb with regs := Function.update sb.regs 18 thr }
  have ra : Runs w p ω (.assign 16 (.load (.reg 87))) s0 .normal sa 3 :=
    runs_assign_iff.mpr ⟨len, by simp [Expr.eval, hr87, hs0Mem, hLenW, len], rfl, rfl, rfl⟩
  have rb : Runs w p ω (.assign 17 (.load (.reg 85))) sa .normal sb 3 :=
    runs_assign_iff.mpr ⟨uc, by simp [Expr.eval, sa, hr85, hs0Mem, hUCW, uc], rfl, rfl, rfl⟩
  have rc : Runs w p ω (.assign 18 (.load (.reg 74))) sb .normal sc 3 :=
    runs_assign_iff.mpr ⟨thr, by simp [Expr.eval, sb, sa, hr74, hs0Mem, hTabW, thr], rfl, rfl,
      rfl⟩
  have hsc : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → sc.regs r = s0.regs r := by
    intro r h1 h2 h3; simp [sc, sb, sa, Function.update, h1, h2, h3]
  have hw : 1 < 2 ^ w := by omega
  have hRest {o : Outcome} {out : State} {c : ℕ} (v : ℕ)
      (hv : (Expr.bin .lt (.reg 18) (.bin .add (.reg 17) (.reg 16))).eval w sc = some v)
      (hrun : Runs w p ω (if v = 0 then branchB else branchA) sc o out c) :
      Runs w p ω (ordChainUpdateCoreBodyKFBL branchA branchB)
        (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos) o out
        (cI + 19 + c) :=
    runs_seq_iff.mpr (Or.inr ⟨s0, cI, c + 18, rI,
      runs_seq_iff.mpr (Or.inr ⟨sa, 3, c + 14, ra,
        runs_seq_iff.mpr (Or.inr ⟨sb, 3, c + 10, rb,
          runs_seq_iff.mpr (Or.inr ⟨sc, 3, c + 6, rc,
            runs_cond_iff.mpr ⟨v, c, hv, hrun, by simp only [Expr.size]; omega⟩, by omega⟩),
          by omega⟩), by omega⟩), by omega⟩)
  refine ⟨sc, cI + 19, hs0Mem, by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, fun o out c => ⟨fun hFire hrun =>
    hRest 1 (by simp [Expr.eval, BinOp.eval, sc, sb, sa, hSumW, hFire, hw, len, uc, thr])
      (by simpa using hrun),
    fun hNo hrun => hRest 0
      (by simp [Expr.eval, BinOp.eval, sc, sb, sa, hSumW, hNo, len, uc, thr])
      (by simpa using hrun)⟩⟩
  all_goals first
    | exact (hsc 4 (by decide) (by decide) (by decide)).trans hr4
    | exact (hsc 70 (by decide) (by decide) (by decide)).trans hr70
    | exact (hsc 71 (by decide) (by decide) (by decide)).trans hr71
    | exact (hsc 72 (by decide) (by decide) (by decide)).trans hr72
    | exact (hsc 73 (by decide) (by decide) (by decide)).trans hr73
    | exact (hsc 74 (by decide) (by decide) (by decide)).trans hr74
    | exact (hsc 75 (by decide) (by decide) (by decide)).trans hr75
    | exact (hsc 76 (by decide) (by decide) (by decide)).trans hr76
    | exact (hsc 77 (by decide) (by decide) (by decide)).trans hr77
    | exact (hsc 78 (by decide) (by decide) (by decide)).trans hr78
    | exact (hsc 79 (by decide) (by decide) (by decide)).trans hr79
    | exact (hsc 80 (by decide) (by decide) (by decide)).trans hr80
    | exact (hsc 81 (by decide) (by decide) (by decide)).trans hr81
    | exact (hsc 82 (by decide) (by decide) (by decide)).trans hr82
    | exact (hsc 83 (by decide) (by decide) (by decide)).trans hr83
    | exact (hsc 84 (by decide) (by decide) (by decide)).trans hr84
    | exact (hsc 85 (by decide) (by decide) (by decide)).trans hr85
    | exact (hsc 86 (by decide) (by decide) (by decide)).trans hr86
    | exact (hsc 87 (by decide) (by decide) (by decide)).trans hr87
    | exact (hsc 88 (by decide) (by decide) (by decide)).trans hr88
    | exact (hsc 89 (by decide) (by decide) (by decide)).trans hr89
    | exact (hsc 90 (by decide) (by decide) (by decide)).trans hr90
    | exact (hsc 91 (by decide) (by decide) (by decide)).trans hr91
    | exact (hsc 92 (by decide) (by decide) (by decide)).trans hr92
    | exact (hsc 93 (by decide) (by decide) (by decide)).trans hr93
    | exact (hsc 94 (by decide) (by decide) (by decide)).trans hr94
    | exact (hsc 95 (by decide) (by decide) (by decide)).trans hr95
    | exact (hsc 98 (by decide) (by decide) (by decide)).trans hr98

/-- The conclusion of `OrdChainUpdateCoreSpecWExtKFBL` for one start state and the core `body`.
The two branches of the chain core each prove it under their test outcome. -/
@[expose] def OrdChainCoreExtPost (w L P m V psi k epsExp drainUnit capExp vCap eCap : ℕ)
    (cfg : Alg2Config) (reembFn : ToolReembFn cfg.T) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (p : Program) (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ) (B_bound R_bound : ℤ)
    (body : Stmt) (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
    (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore)
    (U : List Update) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
  let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
  let modelPre := alg2PreResetState cfg model U gVec lVec
  ∃ nextHeap cost out tok' B' R' firstReb levelU levelUS diffLists,
    Runs w p ω body (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
      (.returned nextHeap) out cost ∧
    heap ≤ nextHeap ∧ nextHeap ≤ heap + coreSpace U.length ∧
    tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
    tok'.rootECap = tok.rootECap ∧ tok'.table = tok.table ∧
    B' ≤ B_bound ∧ R' ≤ R_bound ∧
    Rrep.rep root modelPre tok' out.mem ∧
    SolverLevelMetaAt P V modelPre tok' out.mem ∧
    SolverLevelCapsAt vCap eCap modelPre tok' out.mem ∧
    out.mem (solverLevelMetaAddr tok'.table cfg.P.d + cfg.P.d) = tok'.rootGraph ∧
    PathTreeNumericInv tok'.tree tok'.trees B' R' ∧
    OffTreeRecInv modelPre L out.mem tok'.edgeRecords B' ∧
    OffTreeRecBound modelPre L out.mem tok'.edgeRecords B' ∧
    out.mem (solverSelectHeapAddr tok.table cfg.P.d) =
      mem0 (solverSelectHeapAddr tok.table cfg.P.d) ∧
    out.mem (solverSelectBlocksAddr tok.table cfg.P.d) =
      mem0 (solverSelectBlocksAddr tok.table cfg.P.d) ∧
    UpdateCoreLevelLink model.chain modelPre.chain firstReb levelU levelUS ∧
    UpdateCoreSelectOutAt w P L capExp vCap eCap reembFn (Rrep.foot root tok') out.mem heap
      nextHeap firstReb model.chain modelPre.chain levelU levelUS diffLists ∧
    ZeroFrom out.mem nextHeap ∧
    (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
    (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
    cost + Rrep.phi root tok' out.mem ≤
      coreFixed U.length +
        toolMul * (modelPre.chain.totalRuntime - model.chain.totalRuntime) +
        treeMul * (modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
        40 * (Finset.range (min firstReb cfg.P.d)).sum (fun j => (diffLists j).reemb.length) +
        Rrep.phi root tok mem0

end MinCostFlow.MinRatio
