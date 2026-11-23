module

public import MinCostFlow.MinRatio.UpdateCycleLoopBase
import WordRAM.Tactic

/-!
# Wired candidate-cycle finder (`FindCycleStepSpec`)

Implements the deterministic Word-RAM entry `ordFindCycleWiredBody` for Algorithm 2's
candidate-cycle finder (`[root, heap]`, pages 20 and 29):
1. Reserves the 6-word `CycleDescriptorAt` header at `[heap, heap + 6)`.
2. Invokes `selectRouteProc` (`OrdCycleRouteSelectSpec`), which isolates `algorithm1_findCycle`'s
   `Classical.choose` over the active sparsifier/LSF embeddings of levels `0..d`, writing
   `ExplicitEdgesAt` (`edges`) and `PathEndpointsAt` (`paths`) above `heap + 6` and recording
   `[edgesBase, edgesLen, pathsBase, pathsLen]` at `[heap + 2 .. heap + 5]`.
3. Invokes `evalCycleProc` (`OrdCycleRouteEvalSpec`), which evaluates the signed gradient inner
   product `inner` and nonnegative weighted length `norm` into `[work1, work1 + L)` and
   `[work1 + L, work1 + 2 * L)` using the path tree and off-tree `PathEdgeAt` records.
4. Stores `innerPtr := work1` at `heap` and `normPtr := work1 + L` at `heap + 1`, completing
   the 6-word `CycleDescriptorAt` header and returning `nextHeap`.
5. Proves `findCycleStepSpec_wired`, discharging `FindCycleStepSpec` cleanly.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program

/-- Modular contract for the read-only cycle route extractor
`selectRouteProc [root, descBase, workHeap]` (isolating `algorithm1_findCycle`'s
`Classical.choose` over levels `0..d`). Writes `[edgesBase, edgesLen, pathsBase, pathsLen]`
at `descBase + 2 .. descBase + 5` and the packed edge/path tables inside `[workHeap, work1)`,
leaving `solverStateRep`, `PathTreeNumericInv`, and `OffTreeRecInv` unchanged. -/
@[expose] def OrdCycleRouteSelectSpec (w L P m V psi k epsExp drainUnit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (selectRouteProc selectSpace selectBudget maxEdges maxPaths : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[selectRouteProc]? = some body ∧
    ∀ (root descBase workHeap pos : ℕ) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      Rrep.rep root model tok mem →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      (∀ a, Rrep.foot root tok a → a < descBase) →
      descBase + 6 = workHeap →
      ZeroFrom mem descBase →
      workHeap + selectSpace < 2 ^ w →
      ∃ work1 cost out tok' edges paths,
        Runs w p ω body (startState [root, descBase, workHeap] mem pos) (.returned work1) out cost ∧
        workHeap ≤ work1 ∧ work1 ≤ workHeap + selectSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧
        edges.length ≤ maxEdges ∧ paths.length ≤ maxPaths ∧
        workHeap ≤ out.mem (descBase + 2) ∧
        out.mem (descBase + 2) + 2 * edges.length ≤ work1 ∧
        out.mem (descBase + 3) = edges.length ∧
        workHeap ≤ out.mem (descBase + 4) ∧
        out.mem (descBase + 4) + 2 * paths.length ≤ work1 ∧
        out.mem (descBase + 5) = paths.length ∧
        ExplicitEdgesAt out.mem (out.mem (descBase + 2)) edges ∧
        PathEndpointsAt out.mem (out.mem (descBase + 4)) paths ∧
        CycleRouteAt model edges paths ∧
        (∀ x < 2 * edges.length, ¬ Rrep.foot root tok' (out.mem (descBase + 2) + x)) ∧
        (∀ x < 2 * paths.length, ¬ Rrep.foot root tok' (out.mem (descBase + 4) + x)) ∧
        (∀ a, tok'.tag a = 18 → a < descBase) ∧
        Rrep.rep root model tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem work1 ∧
        (∀ a < descBase, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (workHeap ≤ a ∧ a < work1)) ∧
        cost + Rrep.phi root tok' out.mem ≤ selectBudget + Rrep.phi root tok mem

/-- Modular contract for the cycle inner-product and weighted-length evaluator
`evalCycleProc [root, edgesBase, edgesLen, pathsBase, pathsLen, workHeap]`.
Writes `PathIntAt` for `inner` at `workHeap` and `norm` (`0 ≤ norm`) at `workHeap + L`,
matching `model.extG.inner model.extg Δ` and `model.extG.lnorm model.extℓ Δ`, and returns
`nextHeap` while preserving `solverStateRep`, `PathTreeNumericInv`, `OffTreeRecInv`, and
everything below `workHeap` outside `Rrep.foot`. -/
@[expose] def OrdCycleRouteEvalSpec (w L P m V psi k epsExp drainUnit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (evalCycleProc evalSpace evalBudget maxEdges maxPaths : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[evalCycleProc]? = some body ∧
    ∀ (root edgesBase pathsBase workHeap pos : ℕ) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ)
      (edges : List (ℕ × Bool)) (paths : List (ℕ × ℕ)),
      let Δ := liftEdgeFn model.extG model.extToInt (algorithm1_findCycle model.chain).1
      Rrep.rep root model tok mem →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      edges.length ≤ maxEdges → paths.length ≤ maxPaths →
      ExplicitEdgesAt mem edgesBase edges →
      PathEndpointsAt mem pathsBase paths →
      CycleRouteAt model edges paths →
      edgesBase + 2 * edges.length ≤ workHeap →
      pathsBase + 2 * paths.length ≤ workHeap →
      (∀ x < 2 * edges.length, ¬ Rrep.foot root tok (edgesBase + x)) →
      (∀ x < 2 * paths.length, ¬ Rrep.foot root tok (pathsBase + x)) →
      (∀ a, Rrep.foot root tok a → a < workHeap) →
      ZeroFrom mem workHeap →
      workHeap + evalSpace < 2 ^ w →
      ∃ nextHeap cost out tok' inner norm,
        Runs w p ω body
          (startState [root, edgesBase, edges.length, pathsBase, paths.length, workHeap] mem pos)
          (.returned nextHeap) out cost ∧
        workHeap + 2 * L ≤ nextHeap ∧ nextHeap ≤ workHeap + evalSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧
        0 ≤ norm ∧
        PathIntAt out.mem workHeap 4 L inner ∧
        PathIntAt out.mem (workHeap + L) 4 L norm ∧
        model.extG.inner model.extg Δ = (inner : ℝ) / (2 : ℝ) ^ P ∧
        model.extG.lnorm model.extℓ Δ = (norm : ℝ) / (2 : ℝ) ^ P ∧
        (∀ x < 2 * edges.length, tok'.tag (edgesBase + x) = 0) ∧
        (∀ x < 2 * paths.length, tok'.tag (pathsBase + x) = 0) ∧
        (∀ a, tok'.tag a = 18 → tok.tag a = 18) ∧
        Rrep.rep root model tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < workHeap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (workHeap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤ evalBudget + Rrep.phi root tok mem

/-- Deterministic wired `FindCycle` entry procedure taking `[root, heap]` (`reg 0..1`) and
returning `nextHeap`. Populates the 6-word `CycleDescriptorAt` header at `heap`. -/
@[expose] def ordFindCycleWiredBody (selectRouteProc evalCycleProc : ℕ) : Stmt :=
  .assign 10 (.reg 0) ;;
  .assign 11 (.reg 1) ;;
  .assign 12 (.load (.reg 10)) ;;
  .assign 13 (.load (.bin .add (.reg 12) (.const 5))) ;;
  .assign 14 (.bin .add (.reg 11) (.const 6)) ;;
  .call 15 selectRouteProc [.reg 10, .reg 11, .reg 14] ;;
  .assign 16 (.load (.bin .add (.reg 11) (.const 2))) ;;
  .assign 17 (.load (.bin .add (.reg 11) (.const 3))) ;;
  .assign 18 (.load (.bin .add (.reg 11) (.const 4))) ;;
  .assign 19 (.load (.bin .add (.reg 11) (.const 5))) ;;
  .call 20 evalCycleProc [.reg 10, .reg 16, .reg 17, .reg 18, .reg 19, .reg 15] ;;
  .store (.reg 11) (.reg 15) ;;
  .store (.bin .add (.reg 11) (.const 1)) (.bin .add (.reg 15) (.reg 13)) ;;
  .ret (.reg 20)

theorem ordFindCycleWiredBody_noRand (selectRouteProc evalCycleProc : ℕ) :
    (ordFindCycleWiredBody selectRouteProc evalCycleProc).NoRand := by
  simp [ordFindCycleWiredBody, Stmt.NoRand]

/-- Discharges `FindCycleStepSpec` for `ordFindCycleWiredBody` from `OrdCycleRouteSelectSpec`
and `OrdCycleRouteEvalSpec`. -/
theorem findCycleStepSpec_wired
    {w L P m V psi k epsExp drainUnit findCycleProc selectRouteProc evalCycleProc
      selectSpace selectBudget evalSpace evalBudget maxEdges maxPaths : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    (hlocal : Rcore.Local)
    (hAt : p.procs[findCycleProc]? = some (ordFindCycleWiredBody selectRouteProc evalCycleProc))
    (hSel : OrdCycleRouteSelectSpec w L P m V psi k epsExp drainUnit cfg Rcore p
      selectRouteProc selectSpace selectBudget maxEdges maxPaths)
    (hEval : OrdCycleRouteEvalSpec w L P m V psi k epsExp drainUnit cfg Rcore p
      evalCycleProc evalSpace evalBudget maxEdges maxPaths)
    (hw6 : 6 < 2 ^ w) :
    FindCycleStepSpec w L P m V psi k epsExp drainUnit cfg Rcore p findCycleProc
      (6 + selectSpace + evalSpace) (selectBudget + evalBudget + 90) maxEdges maxPaths := by
  refine ⟨ordFindCycleWiredBody selectRouteProc evalCycleProc, hAt, ?_⟩
  intro root heap pos ω mem model tok B R hrep hnum hoff hbelow hz hroom
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  have hlocR := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocal
  obtain ⟨bSel, hbSel, hSelRun⟩ := hSel
  obtain ⟨bEval, hbEval, hEvalRun⟩ := hEval
  have hrep0 := hrep
  obtain ⟨hrootDir, _, hnumHdr, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, _⟩ := htags
  have hheapW : heap < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have hroot0 : mem root = tok.handle := by simpa using hrootDir 0 (by simp)
  have hL5 : mem (tok.handle + 5) = L := by simpa [Nat.add_assoc] using hnumHdr 0 (by simp)
  have hh5Lt : tok.handle + 5 < 2 ^ w :=
    lt_trans (hbelow _ (Or.inl (hOwn _ (by rw [t2 5 (by omega)]; decide)))) hheapW
  let work0 := heap + 6
  let s0 := startState [root, heap] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 10 root }
  let s2 : State := { s1 with regs := Function.update s1.regs 11 heap }
  let s3 : State := { s2 with regs := Function.update s2.regs 12 tok.handle }
  let s4 : State := { s3 with regs := Function.update s3.regs 13 L }
  let s5 : State := { s4 with regs := Function.update s4.regs 14 work0 }
  have r1 : Runs w p ω (.assign 10 (.reg 0)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 11 (.reg 1)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s1, s0, startState], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 12 (.load (.reg 10))) s2 .normal s3 3 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s2, s1, s0, startState, hroot0], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 12) (.const 5)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, hw5, hh5Lt, hL5], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 14 (.bin .add (.reg 11) (.const 6))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨work0, by simp [Expr.eval, BinOp.eval, s4, s3, s2, hw6, show work0 < 2 ^ w by omega, work0],
      rfl, rfl, rfl⟩
  -- Step 1: call `selectRouteProc`
  obtain ⟨work1, cSel, stSel, tok1, edges, paths, hrSel, hw1Lo, hw1Hi, hlev1, hedMax, hptMax,
      heLo, heHi, heLen, hpLo, hpHi, hpLen, hEdAt, hPtAt, hRoute, hnfEd1, hnfPt1, htag18_1,
      hrep1, hnum1, hoff1, hz1, hfr1, hft1, hcSel⟩ :=
    hSelRun root heap work0 s5.pos ω mem model tok B R hrep0 hnum hoff hbelow rfl hz (by omega)
  let edgesBase := stSel.mem (heap + 2)
  let pathsBase := stSel.mem (heap + 4)
  let s6 : State := { regs := Function.update s5.regs 15 work1, mem := stSel.mem, pos := stSel.pos }
  let s7 : State := { s6 with regs := Function.update s6.regs 16 edgesBase }
  let s8 : State := { s7 with regs := Function.update s7.regs 17 edges.length }
  let s9 : State := { s8 with regs := Function.update s8.regs 18 pathsBase }
  let s10 : State := { s9 with regs := Function.update s9.regs 19 paths.length }
  have r6 : Runs w p ω (.call 15 selectRouteProc [.reg 10, .reg 11, .reg 14]) s5 .normal s6 (cSel + 4) :=
    runs_call_iff.mpr ⟨[root, heap, work0], bSel, .returned work1, stSel, cSel,
      by simp [evalArgs, Expr.eval, s5, s4, s3, s2, s1], hbSel, hrSel, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have r7 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 11) (.const 2)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨edgesBase, by
      simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, hw2, show heap + 2 < 2 ^ w by omega, edgesBase],
      rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 17 (.load (.bin .add (.reg 11) (.const 3)))) s7 .normal s8 5 :=
    runs_assign_iff.mpr ⟨edges.length, by
      simp [Expr.eval, BinOp.eval, s7, s6, s5, s4, s3, s2, hw3, show heap + 3 < 2 ^ w by omega, heLen],
      rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 18 (.load (.bin .add (.reg 11) (.const 4)))) s8 .normal s9 5 :=
    runs_assign_iff.mpr ⟨pathsBase, by
      simp [Expr.eval, BinOp.eval, s8, s7, s6, s5, s4, s3, s2, hw4, show heap + 4 < 2 ^ w by omega, pathsBase],
      rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 11) (.const 5)))) s9 .normal s10 5 :=
    runs_assign_iff.mpr ⟨paths.length, by
      simp [Expr.eval, BinOp.eval, s9, s8, s7, s6, s5, s4, s3, s2, hw5, show heap + 5 < 2 ^ w by omega, hpLen],
      rfl, rfl, rfl⟩
  -- Step 2: call `evalCycleProc`
  have hfoot1_lt (a : ℕ) (ha : Rrep.foot root tok1 a) : a < work1 := by
    rcases hft1 a ha with h0 | ⟨_, hhi⟩
    · have := hbelow a h0; omega
    · exact hhi
  obtain ⟨nextHeap, cEval, stEval, tok2, inner, norm, hrEval, hnhLo, hnhHi, hlev2,
      hnormNN, hinnerAt, hnormAt, hinnerEq, hnormEq, htagEd2, htagPt2, htag18_2,
      hrep2, hnum2, hoff2, hz2, hfr2, hft2, hcEval⟩ :=
    hEvalRun root edgesBase pathsBase work1 s10.pos ω stSel.mem model tok1 B R edges paths
      hrep1 hnum1 hoff1 hedMax hptMax hEdAt hPtAt hRoute heHi hpHi hnfEd1 hnfPt1 hfoot1_lt hz1 (by omega)
  let s11 : State := { regs := Function.update s10.regs 20 nextHeap, mem := stEval.mem, pos := stEval.pos }
  have r11 : Runs w p ω (.call 20 evalCycleProc [.reg 10, .reg 16, .reg 17, .reg 18, .reg 19, .reg 15])
      s10 .normal s11 (cEval + 7) :=
    runs_call_iff.mpr ⟨[root, edgesBase, edges.length, pathsBase, paths.length, work1], bEval,
      .returned nextHeap, stEval, cEval,
      by simp [evalArgs, Expr.eval, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1], hbEval, hrEval,
      rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  -- Step 3: write `innerPtr := work1` at `heap` and `normPtr := work1 + L` at `heap + 1`
  let m12 := Function.update stEval.mem heap work1
  let m13 := Function.update m12 (heap + 1) (work1 + L)
  let s12 : State := { s11 with mem := m12 }
  let s13 : State := { s12 with mem := m13 }
  have r12 : Runs w p ω (.store (.reg 11) (.reg 15)) s11 .normal s12 3 :=
    runs_store_iff.mpr ⟨heap, work1,
      by simp [Expr.eval, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2],
      by simp [Expr.eval, s11, s10, s9, s8, s7, s6], rfl, rfl, rfl⟩
  have r13 : Runs w p ω (.store (.bin .add (.reg 11) (.const 1)) (.bin .add (.reg 15) (.reg 13)))
      s12 .normal s13 7 :=
    runs_store_iff.mpr ⟨heap + 1, work1 + L,
      by simp [Expr.eval, BinOp.eval, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, hw1, show heap + 1 < 2 ^ w by omega],
      by simp [Expr.eval, BinOp.eval, s12, s11, s10, s9, s8, s7, s6, s5, s4, show work1 + L < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have r14 : Runs w p ω (.ret (.reg 20)) s13 (.returned nextHeap) s13 2 :=
    runs_ret_iff.mpr ⟨nextHeap, by simp [Expr.eval, s13, s12, s11], rfl, rfl, rfl⟩
  have rFull : Runs w p ω (ordFindCycleWiredBody selectRouteProc evalCycleProc)
      s0 (.returned nextHeap) s13 _ :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 3, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 4, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, cSel + 4, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 5, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 5, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 5, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, cEval + 7, _, r11,
    runs_seq_iff.mpr (Or.inr ⟨s12, 3, _, r12,
    runs_seq_iff.mpr (Or.inr ⟨s13, 7, 2, r13, r14, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- `heap` and `heap + 1` are strictly outside `Rrep.foot root tok2` and `[work0, nextHeap)`
  have hfoot2_neH (a : ℕ) (ha : Rrep.foot root tok2 a) : a ≠ heap ∧ a ≠ heap + 1 := by
    rcases hft2 a ha with h1 | ⟨hlo, _⟩
    · rcases hft1 a h1 with h0 | ⟨hlo1, _⟩
      · have := hbelow a h0; omega
      · omega
    · omega
  have hneH_m13 (a : ℕ) (h0 : a ≠ heap) (h1 : a ≠ heap + 1) : s13.mem a = stEval.mem a := by
    change Function.update (Function.update stEval.mem heap work1) (heap + 1) (work1 + L) a = _
    rw [Function.update_of_ne h1, Function.update_of_ne h0]
  have hfoot1_notDesc (j : ℕ) (hj : j < 6) : ¬ Rrep.foot root tok1 (heap + j) := fun hf => by
    rcases hft1 _ hf with h0 | ⟨hlo, _⟩
    · have := hbelow _ h0; omega
    · omega
  have hloc2 := hlocR root model tok2 stEval.mem s13.mem (fun a ha => (hneH_m13 a (hfoot2_neH a ha).1 (hfoot2_neH a ha).2).symm)
  have hrepFin : Rrep.rep root model tok2 s13.mem := hloc2.1 hrep2
  have hphiFin : Rrep.phi root tok2 s13.mem = Rrep.phi root tok2 stEval.mem := hloc2.2.symm
  have hoffFin : OffTreeRecInv model L s13.mem tok2.edgeRecords B := by
    have hrep2_0 := hrep2
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags2⟩ := hrep2
    refine offTreeRecInv_of_agree hrep2_0 hoff2 (fun a ha => ?_)
    have hfootA : Rrep.foot root tok2 a :=
      Or.inl (htags2.1 a (by rcases ha with h | h <;> rw [h] <;> decide))
    exact hneH_m13 a (hfoot2_neH a hfootA).1 (hfoot2_neH a hfootA).2
  have hm13_0 : s13.mem heap = work1 := by
    change Function.update (Function.update stEval.mem heap work1) (heap + 1) (work1 + L) heap = work1
    rw [Function.update_of_ne (by omega), Function.update_self]
  have hm13_1 : s13.mem (heap + 1) = work1 + L := by
    change Function.update (Function.update stEval.mem heap work1) (heap + 1) (work1 + L) (heap + 1) = work1 + L
    rw [Function.update_self]
  have hm13_2 : s13.mem (heap + 2) = edgesBase :=
    (hneH_m13 _ (by omega) (by omega)).trans (hfr2 (heap + 2) (by omega) (hfoot1_notDesc 2 (by omega)))
  have hm13_3 : s13.mem (heap + 3) = edges.length :=
    (hneH_m13 _ (by omega) (by omega)).trans ((hfr2 (heap + 3) (by omega) (hfoot1_notDesc 3 (by omega))).trans heLen)
  have hm13_4 : s13.mem (heap + 4) = pathsBase :=
    (hneH_m13 _ (by omega) (by omega)).trans (hfr2 (heap + 4) (by omega) (hfoot1_notDesc 4 (by omega)))
  have hm13_5 : s13.mem (heap + 5) = paths.length :=
    (hneH_m13 _ (by omega) (by omega)).trans ((hfr2 (heap + 5) (by omega) (hfoot1_notDesc 5 (by omega))).trans hpLen)
  have hdescFin : CycleDescriptorAt model L P s13.mem heap nextHeap inner norm edges paths := by
    refine ⟨hm13_3, hm13_5, by omega, by rw [hm13_0]; omega, by rw [hm13_1]; omega,
      by rw [hm13_2]; omega, by rw [hm13_4]; omega,
      by rw [hm13_0]; omega, by rw [hm13_1]; omega,
      by rw [hm13_2]; omega, by rw [hm13_4]; omega, hnormNN, ?_, ?_, hinnerEq, hnormEq, ?_, ?_, hRoute⟩
    · rw [hm13_0]; exact hinnerAt.congr (fun j hj => hneH_m13 _ (by omega) (by omega))
    · rw [hm13_1]; exact hnormAt.congr (fun j hj => hneH_m13 _ (by omega) (by omega))
    · rw [hm13_2]
      exact hEdAt.congr (fun x hlo hhi =>
        (hneH_m13 x (by omega) (by omega)).trans
          (hfr2 x (by omega) (by
            have hx : edgesBase + (x - edgesBase) = x := by omega
            rw [← hx]; exact hnfEd1 (x - edgesBase) (by omega))))
    · rw [hm13_4]
      intro i hi
      have h1 : s13.mem (pathsBase + 2 * i) = stSel.mem (pathsBase + 2 * i) :=
        (hneH_m13 _ (by omega) (by omega)).trans (hfr2 _ (by omega) (hnfPt1 (2 * i) (by omega)))
      have h2 : s13.mem (pathsBase + 2 * i + 1) = stSel.mem (pathsBase + 2 * i + 1) :=
        (hneH_m13 _ (by omega) (by omega)).trans
          (hfr2 _ (by omega) (by
            rw [Nat.add_assoc]; exact hnfPt1 (2 * i + 1) (by omega)))
      exact ⟨h1.trans (hPtAt i hi).1, h2.trans (hPtAt i hi).2⟩
  refine ⟨nextHeap, _, s13, tok2, inner, norm, edges, paths, rFull,
    by omega, by omega, hlev2.trans hlev1, hedMax, hptMax,
    by rw [hm13_2]; exact htagEd2, by rw [hm13_4]; exact htagPt2,
    fun a ha => htag18_1 a (htag18_2 a ha),
    hdescFin, hrepFin, hnum2, hoffFin, ?_, ?_, ?_, ?_⟩
  · intro a ha; exact (hneH_m13 a (by omega) (by omega)).trans (hz2 a ha)
  · intro a ha hnf
    have hnf1 : ¬ Rrep.foot root tok1 a := fun hf => by
      rcases hft1 a hf with h0 | ⟨hlo, _⟩
      · exact hnf h0
      · omega
    exact (hneH_m13 a (by omega) (by omega)).trans ((hfr2 a (by omega) hnf1).trans (hfr1 a ha hnf))
  · intro a ha
    rcases hft2 a ha with h1 | ⟨hlo, hhi⟩
    · rcases hft1 a h1 with h0 | ⟨hlo1, hhi1⟩
      · exact Or.inl h0
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, hhi⟩
  · dsimp only [Rrep] at hcSel hcEval hphiFin ⊢
    rw [hphiFin]; omega

end MinCostFlow.MinRatio
