module

public import MinCostFlow.MinRatio.WireInitLevelsK
public import MinCostFlow.MinRatio.WireInitPostTailK
public import MinCostFlow.MinRatio.InitGraphInput
public import MinCostFlow.MinRatio.InitHeader
public import MinCostFlow.MinRatio.InitTail
public import MinCostFlow.MinRatio.OrdSortedEnds
public import MinCostFlow.MinRatio.InitRootECap
import MinCostFlow.MinRatio.WireChainAlgebra

/-!
# Concrete ordered initializer definition and prefix stages (`WireInitPrefix`)

Defines `initConcreteBody` (and its deterministic witness `initConcreteBody_noRand`), the explicit
space and fixed-cost budgets `initConcreteSpace` and `initConcreteFixed`, and proves Stages 1–2
(`initConcreteStage1_runs`, `initConcreteStage2_runs`, `initConcreteStage2D_runs`):
1. Stage 1 saves caller arguments, reads `(n, m)` from the input graph header, runs parameter
   setup (`initParamSetupContract`) at `pBase = root + 16 + (L + 1) + 6`, loads the chain
   parameters, and computes `eCap = initRootECap N₀ branch m` into register `61`
   (`initComputeRootECap`).
2. Stage 2 packs the root dynamic graph at `rootGraph` with capacities `(G.n, eCap)`, builds
   level-0 `sortedEnds` (`OrdSortedEnds`), initializes `len0Buf` (`eCap * L` words), the level
   metadata region, and the zeroed select-pointer words (`initStage2Meta`), and allocates the
   18-word chain & numeric header at `handle = solverHandleAddr table d = table + (4 * d + 4)`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program LastLevelProgram

/-- Stage 1 of `initConcreteBody`: save caller arguments, read `(n, m)` from the input graph,
run `paramSetup` at `pBase = root + 16 + (L + 1) + 6` (returning `rootGraph` in `reg 7`), load
the chain parameters, and compute `eCap = initRootECap N₀ branch m` into `reg 61`. -/
@[expose] def initConcreteStage1 (paramSetup : ℕ) : Stmt :=
  .assign 69 (.reg 0) ;;
  .assign 70 (.reg 1) ;;
  .assign 71 (.reg 2) ;;
  .assign 67 (.reg 3) ;;
  .assign 68 (.reg 4) ;;
  .assign 95 (.reg 5) ;;
  .assign 97 (.reg 6) ;;
  stageInitSolverGraphSizes ;;
  .assign 58 (.bin .add (.bin .add (.bin .add (.reg 6) (.const 16))
    (.bin .add (.reg 3) (.const 1))) (.const 6)) ;;
  .call 7 paramSetup [.reg 94, .reg 95, .reg 67, .reg 68, .reg 58] ;;
  .assign 75 (.load (.reg 58)) ;;
  .assign 76 (.load (.bin .add (.reg 58) (.const 1))) ;;
  .assign 6 (.load (.bin .add (.reg 58) (.const 2))) ;;
  .assign 72 (.load (.bin .add (.reg 58) (.const 3))) ;;
  .assign 73 (.load (.bin .add (.reg 58) (.const 4))) ;;
  .assign 56 (.load (.bin .add (.reg 58) (.const 5))) ;;
  .assign 57 (.bin .add (.reg 58) (.const 6)) ;;
  initComputeRootECap

/-- Stage 2 of `initConcreteBody`: pack `rootGraph` with capacities `(G.n, eCap)` (saving `reg 94`
in `reg 84` across packing), build level-0 `sortedEnds`, initialize the level-metadata and zeroed
select-pointer region after `table[0..d]`, and allocate the 17-word chain & numeric header at
`handle = solverHandleAddr table d = table + (4 * d + 4)`. -/
@[expose] def initConcreteStage2 (graphPack sortedEnds copy : ℕ) : Stmt :=
  .assign 84 (.reg 94) ;;
  .assign 94 (.reg 61) ;;
  prepareInitSolverGraph graphPack ;;
  .assign 96 (.reg 69) ;;
  .assign 94 (.reg 84) ;;
  .assign 9 (.reg 7) ;;
  .call 7 sortedEnds [.reg 96, .reg 9] ;;
  initStage2Meta copy ;;
  .assign 0 (.reg 94) ;;
  .assign 1 (.reg 95) ;;
  .assign 2 (.reg 67) ;;
  .assign 3 (.reg 68) ;;
  .assign 4 (.bin .add (.reg 97) (.const 16)) ;;
  .assign 78 (.bin .add (.bin .mul (.const 20)
    (.bin .add (.bin .mul (.const 4) (.reg 67)) (.const 8))) (.const 100)) ;;
  .assign 79 (.reg 78) ;;
  allocateMinRatioInitHeader

/-- Stage 2 followed by the store of the sparse-core depth at `handle + 17`. The level table
then starts at `handle + 18`. -/
@[expose] def initConcreteStage2D (graphPack sortedEnds copy : ℕ) : Stmt :=
  initConcreteStage2 graphPack sortedEnds copy ;; storeCoreDepthHeader

/-- Stage 3 of `initConcreteBody`: stage table pointers (including owned `lvlMTable` in `reg 57`,
`levelMeta` in `reg 58`, and owned `len0Buf` in `reg 7`) and execute
`ordRebuildSuffixProgramKFBLStore`. Register `98` holds the sparse-core depth from Stage 2D. -/
@[expose] def initConcreteStage3
    (coreInit coreReadGraph coreReadForest coreLenProc coreReadOrd lastInit : ℕ) : Stmt :=
  .assign 57 (.reg 60) ;;
  .assign 51 (.reg 77) ;;
  .assign 52 (.bin .add (.reg 77) (.bin .add (.reg 75) (.const 1))) ;;
  .assign 4 (.bin .add (.reg 52) (.bin .add (.reg 75) (.const 1))) ;;
  .assign 1 (.reg 76) ;;
  .assign 6 (.reg 96) ;;
  .assign 7 (.reg 59) ;;
  .assign 8 (.reg 70) ;;
  .assign 20 (.const 0) ;;
  .assign 21 (.reg 75) ;;
  ordRebuildSuffixProgramKFBLStore coreInit coreReadGraph coreReadForest coreLenProc coreReadOrd
    lastInit

/-- Full deterministic concrete ordered initializer (`initConcreteProc`). -/
@[expose] def initConcreteBody
    (graphPack paramSetup sortedEnds coreInit coreReadGraph coreReadForest coreLenProc
      coreReadOrd lastInit lastReadout treeInit treeLink bind shift divide negate copy : ℕ) : Stmt :=
  initConcreteStage1 paramSetup ;;
  initConcreteStage2D graphPack sortedEnds copy ;;
  initConcreteStage3 coreInit coreReadGraph coreReadForest coreLenProc coreReadOrd lastInit ;;
  .assign 69 (.reg 96) ;;
  finishSolverInitBody treeInit ;;
  solverInitPostTailBodyAt 18 shift divide negate copy coreReadForest coreReadGraph lastReadout
    treeLink bind ;;
  .ret (.reg 99)

theorem initConcreteBody_noRand
    (graphPack paramSetup sortedEnds coreInit coreReadGraph coreReadForest coreLenProc
      coreReadOrd lastInit lastReadout treeInit treeLink bind shift divide negate copy : ℕ) :
    (initConcreteBody graphPack paramSetup sortedEnds coreInit coreReadGraph coreReadForest
      coreLenProc coreReadOrd lastInit lastReadout treeInit treeLink bind shift divide negate copy).NoRand := by
  simp [initConcreteBody, initConcreteStage1, initConcreteStage2D, initConcreteStage2,
    initStage2Meta_noRand, initComputeRootECap_noRand, storeCoreDepthHeader, initConcreteStage3,
    stageInitSolverGraphSizes, prepareInitSolverGraph,
    packInitSolverGraph, advanceInitSolverGraphHeap,
    allocateMinRatioInitHeader, allocateChainInitHeader, storeChainInitParameters,
    storeMinRatioNumericHeader,
    ordRebuildSuffixProgramKFBLStore_noRand,
    finishSolverInitBody_noRand, solverInitPostTailBodyAt_noRand, Stmt.NoRand]

/-- Total heap space allocated above `root` by `initConcreteBody`. -/
@[expose] def initConcreteSpace (m n L d paramSpace capExp capLimit lastSpace
    treeInitSpace linkSpace : ℕ) (coreInitSpace lvlM nextM : ℕ → ℕ) (N₀ : ℕ) : ℕ :=
  16 + (L + 1) + 6 + paramSpace + dynGraphSize n capLimit +
    (1 + 4 * n + 2 * capLimit) + capLimit * L + (4 * d + 4) + 18 + (d + 1) + (d + 1) +
    ordInitLevelsSpace L capExp capLimit coreInitSpace lvlM nextM N₀ lastSpace d +
    (4 * (d + 1) + 1) + 1 + 3 * m + treeInitSpace +
    initPostTailSpace m n L d linkSpace

/-- Fixed step cost of `initConcreteBody` (excluding `max P.mul lastMult * totalRuntime`). -/
@[expose] def initConcreteFixed (m n L d paramCost capExp capLimit lastMult
    treeConst : ℕ) (P : SparseCoreOrdParams) (lvlM nextM : ℕ → ℕ) (N₀ : ℕ) : ℕ :=
  (130 * n + 490 * m + 145) + paramCost + (150 * capLimit + 60 * n + 120) +
    ordInitLevelsFixed L capExp capLimit P lvlM nextM N₀ lastMult d +
    (treeConst * (L + 1) ^ 2 * (n + 1) + 20 * m + 92) +
    initPostTailCost m n L d treeConst P.readout + 30 * (m * L) + 56 * d +
    22 * Nat.clog 2 (N₀ + 2) + 1000

theorem initConcreteStage1_runs
    {w paramSetup graph gradient lengths L P V root pos d branch psi k epsExp
      N₀ coreDepth paramSpace paramCost : ℕ}
    {lvlM : ℕ → ℕ} {G : MGraph} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hparam : MeetsContract w p paramSetup
      (initParamSetupContract w G.m V L P d branch psi k epsExp N₀ coreDepth lvlM paramSpace
        paramCost))
    (hG : GraphAt mem graph G)
    (hGraphBelow : graph + (graphWords G).length ≤ root)
    (hz : ZeroFrom mem root) (hbrPos : 0 < branch)
    (hVW : V < 2 ^ w) (hPW : P < 2 ^ w) (hN3w : N₀ + 3 < 2 ^ w)
    (heCapW : initRootECap N₀ branch G.m < 2 ^ w) (hw17 : 17 < 2 ^ w)
    (hroom : root + 16 + (L + 1) + 6 + paramSpace < 2 ^ w) :
    let pBase := root + 16 + (L + 1) + 6
    let eCap := initRootECap N₀ branch G.m
    ∃ s1 rootGraph c1,
      Runs w p ω (initConcreteStage1 paramSetup)
        (startState [graph, gradient, lengths, L, P, V, root] mem pos) .normal s1 c1 ∧
      pBase + 7 + d ≤ rootGraph ∧ rootGraph ≤ pBase + paramSpace ∧
      s1.regs 6 = psi ∧ s1.regs 7 = rootGraph ∧ s1.regs 56 = N₀ ∧ s1.regs 57 = pBase + 6 ∧
      s1.regs 61 = eCap ∧ s1.regs 67 = L ∧ s1.regs 68 = P ∧ s1.regs 69 = graph ∧
      s1.regs 70 = gradient ∧ s1.regs 71 = lengths ∧ s1.regs 72 = k ∧ s1.regs 73 = epsExp ∧
      s1.regs 75 = d ∧ s1.regs 76 = branch ∧ s1.regs 92 = G.n ∧ s1.regs 93 = G.n ∧
      s1.regs 94 = G.m ∧ s1.regs 95 = V ∧ s1.regs 97 = root ∧
      (∀ i < d, s1.mem (pBase + 6 + i) = lvlM i) ∧ s1.mem (pBase + 6 + d) = coreDepth ∧
      (∀ a < pBase, s1.mem a = mem a) ∧ ZeroFrom s1.mem rootGraph ∧
      c1 ≤ paramCost + 22 * Nat.clog 2 (N₀ + 2) + 150 := by
  intro pBase eCap
  let st0 := startState [graph, gradient, lengths, L, P, V, root] mem pos
  have hr0 : st0.regs 0 = graph := rfl
  have hr1 : st0.regs 1 = gradient := rfl
  have hr2 : st0.regs 2 = lengths := rfl
  have hr3 : st0.regs 3 = L := rfl
  have hr4 : st0.regs 4 = P := rfl
  have hr5 : st0.regs 5 = V := rfl
  have hr6 : st0.regs 6 = root := rfl
  let a1 := { st0 with regs := Function.update st0.regs 69 graph }
  let a2 := { a1 with regs := Function.update a1.regs 70 gradient }
  let a3 := { a2 with regs := Function.update a2.regs 71 lengths }
  let a4 := { a3 with regs := Function.update a3.regs 67 L }
  let a5 := { a4 with regs := Function.update a4.regs 68 P }
  let a6 := { a5 with regs := Function.update a5.regs 95 V }
  let a7 := { a6 with regs := Function.update a6.regs 97 root }
  have r1 : Runs w p ω (.assign 69 (.reg 0)) st0 .normal a1 2 :=
    runs_assign_iff.mpr ⟨graph, by simp [Expr.eval, hr0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 70 (.reg 1)) a1 .normal a2 2 :=
    runs_assign_iff.mpr ⟨gradient, by simp [Expr.eval, a1, hr1], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 71 (.reg 2)) a2 .normal a3 2 :=
    runs_assign_iff.mpr ⟨lengths, by simp [Expr.eval, a2, a1, hr2], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 67 (.reg 3)) a3 .normal a4 2 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, a3, a2, a1, hr3], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 68 (.reg 4)) a4 .normal a5 2 :=
    runs_assign_iff.mpr ⟨P, by simp [Expr.eval, a4, a3, a2, a1, hr4], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 95 (.reg 5)) a5 .normal a6 2 :=
    runs_assign_iff.mpr ⟨V, by simp [Expr.eval, a5, a4, a3, a2, a1, hr5], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 97 (.reg 6)) a6 .normal a7 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, a6, a5, a4, a3, a2, a1, hr6], rfl, rfl, rfl⟩
  have hgraph1W : graph + 1 < 2 ^ w := by
    have hlen : 2 ≤ (graphWords G).length := by simp [graphWords]
    omega
  obtain ⟨a8, r8, ha8_92, ha8_93, ha8_94, ha8_keep, ha8_mem, _⟩ :=
    stageInitSolverGraphSizes_runs (w := w) (graph := graph) (G := G) (p := p) (ω := ω) (st := a7)
      (by simp [a7, a6, a5, a4, a3, a2, a1]) hG hgraph1W
  have ha8_r (r : ℕ) (h92 : r ≠ 92 := by decide) (h93 : r ≠ 93 := by decide)
      (h94 : r ≠ 94 := by decide) : a8.regs r = a7.regs r := ha8_keep r h92 h93 h94
  let a9 := { a8 with regs := Function.update a8.regs 58 pBase }
  have r9 : Runs w p ω (.assign 58 (.bin .add (.bin .add (.bin .add (.reg 6) (.const 16))
      (.bin .add (.reg 3) (.const 1))) (.const 6))) a8 .normal a9 10 :=
    runs_assign_iff.mpr ⟨pBase, by
      simp [Expr.eval, BinOp.eval, ha8_r 6, ha8_r 3, a7, a6, a5, a4, a3, a2, a1, hr6, hr3, pBase,
        show 1 < 2 ^ w by omega, show 6 < 2 ^ w by omega, show 16 < 2 ^ w by omega,
        show root + 16 < 2 ^ w by omega, show L + 1 < 2 ^ w by omega,
        show root + 16 + (L + 1) < 2 ^ w by omega, show root + 16 + (L + 1) + 6 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hGmW : G.m < 2 ^ w := lt_of_le_of_lt (initRootECap_ge_m N₀ branch G.m) heCapW
  have hargsP : evalArgs w a9 [.reg 94, .reg 95, .reg 67, .reg 68, .reg 58] =
      some [G.m, V, L, P, pBase] := by
    simp [evalArgs, Expr.eval, a9, ha8_94, ha8_r 95, ha8_r 67, ha8_r 68, a7, a6, a5, a4]
  have hwordsP : ∀ v ∈ [G.m, V, L, P, pBase], v < 2 ^ w := by
    intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨b2, cP, rootGraph, rb2, hpostP, hb2_7, hb2_keep, hcP⟩ :=
    runs_call_of_meetsContract (r := 7) hparam hargsP hwordsP
      ⟨pBase, rfl, fun a ha => ha8_mem.symm ▸ hz a (by omega), by omega⟩ ω
  obtain ⟨hordLo, hordHi, hplist, hlvlM, hdepthP, hframeP, hzRG⟩ := hpostP
  simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some] at hordLo hordHi hplist hlvlM hdepthP hframeP hzRG
  simp only [initParamSetupContract, argsSize, Expr.size] at hcP
  have hpMem (j : ℕ) (hj : j < 6) : b2.mem (pBase + j) = [d, branch, psi, k, epsExp, N₀][j] :=
    hplist j (by simpa using hj)
  have hb2_58 : b2.regs 58 = pBase := (hb2_keep 58 (by decide)).trans (by simp [a9])
  let b3 := { b2 with regs := Function.update b2.regs 75 d }
  let b4 := { b3 with regs := Function.update b3.regs 76 branch }
  let b5 := { b4 with regs := Function.update b4.regs 6 psi }
  let b6 := { b5 with regs := Function.update b5.regs 72 k }
  let b7 := { b6 with regs := Function.update b6.regs 73 epsExp }
  let b8 := { b7 with regs := Function.update b7.regs 56 N₀ }
  let b9 := { b8 with regs := Function.update b8.regs 57 (pBase + 6) }
  have rb3 : Runs w p ω (.assign 75 (.load (.reg 58))) b2 .normal b3 3 :=
    runs_assign_iff.mpr ⟨d, by simp [Expr.eval, hb2_58]; exact hpMem 0 (by decide), rfl, rfl, rfl⟩
  have rb4 : Runs w p ω (.assign 76 (.load (.bin .add (.reg 58) (.const 1)))) b3 .normal b4 5 :=
    runs_assign_iff.mpr ⟨branch, by
      simp [Expr.eval, BinOp.eval, b3, hb2_58, show 1 < 2 ^ w by omega,
        show pBase + 1 < 2 ^ w by omega]; exact hpMem 1 (by decide), rfl, rfl, rfl⟩
  have rb5 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 58) (.const 2)))) b4 .normal b5 5 :=
    runs_assign_iff.mpr ⟨psi, by
      simp [Expr.eval, BinOp.eval, b4, b3, hb2_58, show 2 < 2 ^ w by omega,
        show pBase + 2 < 2 ^ w by omega]; exact hpMem 2 (by decide), rfl, rfl, rfl⟩
  have rb6 : Runs w p ω (.assign 72 (.load (.bin .add (.reg 58) (.const 3)))) b5 .normal b6 5 :=
    runs_assign_iff.mpr ⟨k, by
      simp [Expr.eval, BinOp.eval, b5, b4, b3, hb2_58, show 3 < 2 ^ w by omega,
        show pBase + 3 < 2 ^ w by omega]; exact hpMem 3 (by decide), rfl, rfl, rfl⟩
  have rb7 : Runs w p ω (.assign 73 (.load (.bin .add (.reg 58) (.const 4)))) b6 .normal b7 5 :=
    runs_assign_iff.mpr ⟨epsExp, by
      simp [Expr.eval, BinOp.eval, b6, b5, b4, b3, hb2_58, show 4 < 2 ^ w by omega,
        show pBase + 4 < 2 ^ w by omega]; exact hpMem 4 (by decide), rfl, rfl, rfl⟩
  have rb8 : Runs w p ω (.assign 56 (.load (.bin .add (.reg 58) (.const 5)))) b7 .normal b8 5 :=
    runs_assign_iff.mpr ⟨N₀, by
      simp [Expr.eval, BinOp.eval, b7, b6, b5, b4, b3, hb2_58, show 5 < 2 ^ w by omega,
        show pBase + 5 < 2 ^ w by omega]; exact hpMem 5 (by decide), rfl, rfl, rfl⟩
  have rb9 : Runs w p ω (.assign 57 (.bin .add (.reg 58) (.const 6))) b8 .normal b9 4 :=
    runs_assign_iff.mpr ⟨pBase + 6, by
      simp [Expr.eval, BinOp.eval, b8, b7, b6, b5, b4, b3, hb2_58, show 6 < 2 ^ w by omega,
        show pBase + 6 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hb9_94 : b9.regs 94 = G.m := by
    simp only [b9, b8, b7, b6, b5, b4, b3, Function.update_of_ne (by decide : (94 : ℕ) ≠ 57),
      Function.update_of_ne (by decide : (94 : ℕ) ≠ 56), Function.update_of_ne (by decide : (94 : ℕ) ≠ 73),
      Function.update_of_ne (by decide : (94 : ℕ) ≠ 72), Function.update_of_ne (by decide : (94 : ℕ) ≠ 6),
      Function.update_of_ne (by decide : (94 : ℕ) ≠ 76), Function.update_of_ne (by decide : (94 : ℕ) ≠ 75)]
    exact (hb2_keep 94 (by decide)).trans (by simp [a9, ha8_94])
  obtain ⟨s1, cECap, rECap, hs1_61, hs1_mem, _, hs1_keep, hcECap⟩ :=
    initComputeRootECap_runs (w := w) (N₀ := N₀) (k := branch) (m := G.m) (p := p) (ω := ω) (st := b9)
      (by simp [b9, b8]) (by simp [b9, b8, b7, b6, b5, b4]) hb9_94 hbrPos hw17 hN3w heCapW
  have hrFull : Runs w p ω (initConcreteStage1 paramSetup) st0 .normal s1
      (2 + (2 + (2 + (2 + (2 + (2 + (2 + (12 + (10 + (cP + (3 + (5 + (5 + (5 + (5 + (5 +
        (4 + cECap + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨a1, 2, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨a2, 2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨a3, 2, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨a4, 2, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨a5, 2, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨a6, 2, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨a7, 2, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨a8, 12, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨a9, 10, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨b2, cP, _, rb2,
    runs_seq_iff.mpr (Or.inr ⟨b3, 3, _, rb3,
    runs_seq_iff.mpr (Or.inr ⟨b4, 5, _, rb4,
    runs_seq_iff.mpr (Or.inr ⟨b5, 5, _, rb5,
    runs_seq_iff.mpr (Or.inr ⟨b6, 5, _, rb6,
    runs_seq_iff.mpr (Or.inr ⟨b7, 5, _, rb7,
    runs_seq_iff.mpr (Or.inr ⟨b8, 5, _, rb8,
    runs_seq_iff.mpr (Or.inr ⟨b9, 4, cECap, rb9, rECap, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hs1_b9 (r : ℕ) (h10 : r ≠ 10 := by decide) (h11 : r ≠ 11 := by decide)
      (h12 : r ≠ 12 := by decide) (h61 : r ≠ 61 := by decide) : s1.regs r = b9.regs r :=
    hs1_keep r h10 h11 h12 h61
  have hb9_a8 (r : ℕ) (h57 : r ≠ 57 := by decide) (h56 : r ≠ 56 := by decide)
      (h73 : r ≠ 73 := by decide) (h72 : r ≠ 72 := by decide) (h6 : r ≠ 6 := by decide)
      (h76 : r ≠ 76 := by decide) (h75 : r ≠ 75 := by decide) (h7 : r ≠ 7 := by decide)
      (h58 : r ≠ 58 := by decide) : b9.regs r = a8.regs r := by
    simp only [b9, b8, b7, b6, b5, b4, b3, Function.update_of_ne h57, Function.update_of_ne h56,
      Function.update_of_ne h73, Function.update_of_ne h72, Function.update_of_ne h6,
      Function.update_of_ne h76, Function.update_of_ne h75]
    exact (hb2_keep r h7).trans (by simp [a9, Function.update_of_ne h58])
  refine ⟨s1, rootGraph, _, hrFull, hordLo, hordHi,
    (hs1_b9 6).trans (by simp [b9, b8, b7, b6, b5]),
    (hs1_b9 7).trans (by simp [b9, b8, b7, b6, b5, b4, b3, hb2_7]),
    (hs1_b9 56).trans (by simp [b9, b8]),
    (hs1_b9 57).trans (by simp [b9]),
    hs1_61,
    (hs1_b9 67).trans ((hb9_a8 67).trans ((ha8_r 67).trans (by simp [a7, a6, a5, a4]))),
    (hs1_b9 68).trans ((hb9_a8 68).trans ((ha8_r 68).trans (by simp [a7, a6, a5]))),
    (hs1_b9 69).trans ((hb9_a8 69).trans ((ha8_r 69).trans (by simp [a7, a6, a5, a4, a3, a2, a1]))),
    (hs1_b9 70).trans ((hb9_a8 70).trans ((ha8_r 70).trans (by simp [a7, a6, a5, a4, a3, a2]))),
    (hs1_b9 71).trans ((hb9_a8 71).trans ((ha8_r 71).trans (by simp [a7, a6, a5, a4, a3]))),
    (hs1_b9 72).trans (by simp [b9, b8, b7, b6]),
    (hs1_b9 73).trans (by simp [b9, b8, b7]),
    (hs1_b9 75).trans (by simp [b9, b8, b7, b6, b5, b4, b3]),
    (hs1_b9 76).trans (by simp [b9, b8, b7, b6, b5, b4]),
    (hs1_b9 92).trans ((hb9_a8 92).trans ha8_92),
    (hs1_b9 93).trans ((hb9_a8 93).trans ha8_93),
    (hs1_b9 94).trans hb9_94,
    (hs1_b9 95).trans ((hb9_a8 95).trans ((ha8_r 95).trans (by simp [a7, a6]))),
    (hs1_b9 97).trans ((hb9_a8 97).trans ((ha8_r 97).trans (by simp [a7]))),
    fun i hi => by rw [hs1_mem]; exact hlvlM i hi,
    by rw [hs1_mem]; exact hdepthP,
    fun a ha => by rw [hs1_mem, hframeP a ha, ha8_mem]; rfl,
    by rw [hs1_mem]; exact hzRG,
    by omega⟩

set_option maxHeartbeats 600000 in
/-- Stage 2 runs: packs `rootGraph` with capacities `(G.n, eCap)`, builds level-0 `sortedEnds`,
populates `len0Buf` (`eCap * L` words), level metadata, and zeroed select-pointer words, and
allocates the 17-word chain & numeric header at `solverHandleAddr table d = table + (4 * d + 4)`. -/
theorem initConcreteStage2_runs
    {w graphPack sortedEnds copy root pBase rootGraph graph gradient lengths m eCap V L P d
      branch psi k epsExp N₀ coreDepth : ℕ}
    {lvlM : ℕ → ℕ} {G : MGraph} {p : Program} {ω : ℕ → Bool} {st : State}
    (hpack : MeetsContract w p graphPack
      (dgInitFromListsContract w G.n eCap G (G.V.sort (· ≤ ·))
        ((G.E.sort (· ≤ ·)).map (fun e => (e, G.tail e, G.head e)))))
    (hsortAt : p.procs[sortedEnds]? = some buildSortedEndsBody)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h6 : st.regs 6 = psi) (h7 : st.regs 7 = rootGraph) (h56 : st.regs 56 = N₀)
    (h57 : st.regs 57 = pBase + 6) (h61 : st.regs 61 = eCap) (h67 : st.regs 67 = L)
    (h68 : st.regs 68 = P) (h69 : st.regs 69 = graph) (h70 : st.regs 70 = gradient)
    (h71 : st.regs 71 = lengths) (h72 : st.regs 72 = k) (h73 : st.regs 73 = epsExp)
    (h75 : st.regs 75 = d) (h76 : st.regs 76 = branch) (h93 : st.regs 93 = G.n)
    (h94 : st.regs 94 = m) (h95 : st.regs 95 = V) (h97 : st.regs 97 = root)
    (hG : GraphAt st.mem graph G) (hGV : G.IsValid) (hGm : G.m = m)
    (hVlt : ∀ v ∈ G.V, v < G.n) (hElt : ∀ e ∈ G.E, e < eCap) (hmLeECap : m ≤ eCap)
    (hGraphBelow : graph + (graphWords G).length ≤ root)
    (hLenBelow : lengths + m * L ≤ root)
    (hroot16 : root + 16 ≤ pBase)
    (hpBaseLe : pBase + 7 + d ≤ rootGraph)
    (hMTab : ∀ i < d, st.mem (pBase + 6 + i) = lvlM i)
    (hDepth : st.mem (pBase + 6 + d) = coreDepth)
    (hz : ZeroFrom st.mem rootGraph)
    (hNw : N₀ < 2 ^ w) (hdPos : 0 < d) (hsearchW : 20 * (4 * L + 8) + 100 < 2 ^ w)
    (hw17 : 17 < 2 ^ w)
    (hroom : rootGraph + dynGraphSize G.n eCap + (1 + 4 * G.n + 2 * eCap) + eCap * L +
      (4 * d + 4) + 17 < 2 ^ w) :
    let ordBase := rootGraph + dynGraphSize G.n eCap
    let len0Buf := ordBase + 1 + 4 * G.n + 2 * eCap
    let table := len0Buf + eCap * L
    let handle := solverHandleAddr table d
    ∃ s2 c2,
      Runs w p ω (initConcreteStage2 graphPack sortedEnds copy) st .normal s2 c2 ∧
      s2.regs 9 = ordBase ∧ s2.regs 56 = N₀ ∧ s2.regs 57 = pBase + 6 ∧
      s2.regs 58 = solverLevelMetaAddr table d ∧ s2.regs 59 = len0Buf ∧
      s2.regs 60 = solverLvlMAddr table d ∧
      s2.regs 67 = L ∧ s2.regs 68 = P ∧ s2.regs 70 = gradient ∧ s2.regs 71 = lengths ∧
      s2.regs 74 = handle ∧ s2.regs 75 = d ∧ s2.regs 76 = branch ∧
      s2.regs 77 = handle + 17 ∧ s2.regs 96 = rootGraph ∧
      DynGraphAt s2.mem rootGraph G.n eCap G ∧
      (∀ i < d, s2.mem (pBase + 6 + i) = lvlM i) ∧ s2.mem (pBase + 6 + d) = coreDepth ∧
      s2.mem (solverN0Addr table d) = N₀ ∧
      (∀ i < d, s2.mem (solverLvlMAddr table d + i) = lvlM i) ∧
      s2.mem (solverLevelMetaAddr table d) = len0Buf ∧
      s2.mem (solverLevelMetaAddr table d + d) = rootGraph ∧
      s2.mem (solverSelectHeapAddr table d) = 0 ∧
      s2.mem (solverSelectBlocksAddr table d) = 0 ∧
      (∀ j < m * L, s2.mem (len0Buf + j) = st.mem (lengths + j)) ∧
      OrdListAt s2.mem ordBase (Bundle.sortedEnds G) (1 + 2 * G.n + 2 * m) ∧
      (∀ j < 1 + 2 * G.n + 2 * m, s2.mem (ordBase + j) < 2 ^ w) ∧
      ChainInitParametersAt s2.mem handle m V d branch psi (root + 16) k epsExp ∧
      MinRatioNumericHeaderAt s2.mem handle L P (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
      (∀ a < rootGraph, s2.mem a = st.mem a) ∧
      ZeroFrom s2.mem (handle + 17) ∧
      c2 ≤ (130 * G.n + 490 * m) + (150 * eCap + 60 * G.n) + 30 * (m * L) + 30 * d + 590 := by
  intro ordBase len0Buf table handle
  have hhandleDef : handle = table + (4 * d + 4) := by
    unfold handle solverHandleAddr solverSelectBlocksAddr solverSelectHeapAddr
      solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega
  let p1 := { st with regs := Function.update st.regs 84 m }
  let p2 := { p1 with regs := Function.update p1.regs 94 eCap }
  have rp1 : Runs w p ω (.assign 84 (.reg 94)) st .normal p1 2 :=
    runs_assign_iff.mpr ⟨m, by simp [Expr.eval, h94], rfl, rfl, rfl⟩
  have rp2 : Runs w p ω (.assign 94 (.reg 61)) p1 .normal p2 2 :=
    runs_assign_iff.mpr ⟨eCap, by simp [Expr.eval, p1, h61], rfl, rfl, rfl⟩
  obtain ⟨p3, cPack, rPack, hp3_69, hp3_7, hDG3, hframePack, hzOrd, hp3_keep, hcPack⟩ :=
    prepareInitSolverGraph_runs (w := w) (entry := graphPack) (graph := graph)
      (heap := rootGraph) (vc := G.n) (ec := eCap) (mem := st.mem) (G := G) (p := p) (ω := ω) (st := p2)
      rfl hpack hG hGV (by simp [p2, p1, h69]) (by simp [p2, p1, h7])
      (by simp [p2, p1, h93]) (by simp [p2]) hVlt hElt (by omega) hz (by omega) (by omega)
  let b1 := { p3 with regs := Function.update p3.regs 96 rootGraph }
  let b2 := { b1 with regs := Function.update b1.regs 94 m }
  let b9 := { b2 with regs := Function.update b2.regs 9 ordBase }
  have rb1 : Runs w p ω (.assign 96 (.reg 69)) p3 .normal b1 2 :=
    runs_assign_iff.mpr ⟨rootGraph, by simp [Expr.eval, hp3_69], rfl, rfl, rfl⟩
  have hp3_84 : p3.regs 84 = m := (hp3_keep 84 (by decide) (by decide)).trans (by simp [p2, p1])
  have rb2 : Runs w p ω (.assign 94 (.reg 84)) b1 .normal b2 2 :=
    runs_assign_iff.mpr ⟨m, by simp [Expr.eval, b1, hp3_84], rfl, rfl, rfl⟩
  have rb9 : Runs w p ω (.assign 9 (.reg 7)) b2 .normal b9 2 :=
    runs_assign_iff.mpr ⟨ordBase, by simp [Expr.eval, b2, b1, hp3_7, ordBase], rfl, rfl, rfl⟩
  obtain ⟨cSort, sSort, rSortBody, hcSort, _, hOrdAt, _, hOrdW, hzLen0, hframeSort⟩ :=
    buildSortedEndsBody_runs (w := w) (graph := rootGraph) (out := ordBase) (vCap := G.n)
      (eCap := eCap) (pos := b9.pos) (p := p) (ω := ω) (mem := p3.mem) (G := G)
      hDG3 (by omega) hzOrd (by omega) (by omega)
  let b10 : State := { sSort with regs := Function.update b9.regs 7 len0Buf }
  have hargsS : evalArgs w b9 [.reg 96, .reg 9] = some [rootGraph, ordBase] := by
    simp [evalArgs, Expr.eval, b9, b2, b1]
  have rb10 : Runs w p ω (.call 7 sortedEnds [.reg 96, .reg 9]) b9 .normal b10 (2 + cSort + 1) :=
    runs_call_iff.mpr ⟨[rootGraph, ordBase], buildSortedEndsBody, .returned len0Buf, sSort, cSort,
      hargsS, hsortAt, by simpa [b9, b2, b1, len0Buf] using rSortBody, rfl, rfl, rfl⟩
  have hb10_r (r : ℕ) (h7' : r ≠ 7 := by decide) (h9 : r ≠ 9 := by decide)
      (h69' : r ≠ 69 := by decide) (h84 : r ≠ 84 := by decide) (h94' : r ≠ 94 := by decide)
      (h96 : r ≠ 96 := by decide) : b10.regs r = st.regs r := by
    simp only [b10, b9, b2, b1, Function.update_of_ne h7', Function.update_of_ne h9,
      Function.update_of_ne h94', Function.update_of_ne h96]
    exact (hp3_keep r h69' h7').trans (by simp [p2, p1, Function.update_of_ne h94', Function.update_of_ne h84])
  have hb10_mem_below (a : ℕ) (ha : a < rootGraph) : b10.mem a = st.mem a :=
    (hframeSort a (by omega)).trans (hframePack a ha)
  have hb10_MTab (i : ℕ) (hi : i < d) : b10.mem (pBase + 6 + i) = lvlM i :=
    (hb10_mem_below _ (by omega)).trans (hMTab i hi)
  obtain ⟨c1, cMeta, rcMeta, hc1_7, hc1_58, hc1_59, hc1_60, hc1_keep,
      hc1_len0, hc1_n0, hc1_lvlM, hc1_meta0, hc1_metaG0, hc1_sh, hc1_sb, hc1_frame, hzHandle, hcMeta⟩ :=
    initStage2Meta_runs (w := w) (copy := copy) (root := root) (rootGraph := rootGraph)
      (pBase := pBase) (lengths := lengths) (len0Buf := len0Buf) (m := m) (eCap := eCap) (L := L)
      (d := d) (N₀ := N₀) (lvlM := lvlM) (p := p) (ω := ω) (st := b10)
      hcopy (by simp [b10]) ((hb10_r 56).trans h56) ((hb10_r 57).trans h57)
      ((hb10_r 61).trans h61) ((hb10_r 67).trans h67) ((hb10_r 71).trans h71)
      ((hb10_r 75).trans h75) (by simp [b10, b9, b2]) (by simp [b10, b9, b2, b1])
      hmLeECap hLenBelow (by omega) (by omega) hb10_MTab hNw hdPos hw17
      (fun a ha => by simpa [b10] using hzLen0 a (by omega)) (by omega)
  let sp := 20 * (4 * L + 8) + 100
  let c2s := { c1 with regs := Function.update c1.regs 0 m }
  let c3 := { c2s with regs := Function.update c2s.regs 1 V }
  let c4 := { c3 with regs := Function.update c3.regs 2 L }
  let c5 := { c4 with regs := Function.update c4.regs 3 P }
  let c6 := { c5 with regs := Function.update c5.regs 4 (root + 16) }
  let c7 := { c6 with regs := Function.update c6.regs 78 sp }
  let c8 := { c7 with regs := Function.update c7.regs 79 sp }
  have hc1_st (r : ℕ) (h0 : r ≠ 0 := by decide) (h7' : r ≠ 7 := by decide)
      (h9 : r ≠ 9 := by decide) (h10 : r ≠ 10 := by decide) (h58 : r ≠ 58 := by decide)
      (h59 : r ≠ 59 := by decide) (h60 : r ≠ 60 := by decide) (h69' : r ≠ 69 := by decide)
      (h84 : r ≠ 84 := by decide) (h94' : r ≠ 94 := by decide) (h96 : r ≠ 96 := by decide) :
      c1.regs r = st.regs r :=
    (hc1_keep r h0 h7' h10 h58 h59 h60).trans (hb10_r r h7' h9 h69' h84 h94' h96)
  have hc1_94 : c1.regs 94 = m :=
    (hc1_keep 94 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simp [b10, b9, b2])
  have rc2 : Runs w p ω (.assign 0 (.reg 94)) c1 .normal c2s 2 :=
    runs_assign_iff.mpr ⟨m, by simp [Expr.eval, hc1_94], rfl, rfl, rfl⟩
  have rc3 : Runs w p ω (.assign 1 (.reg 95)) c2s .normal c3 2 :=
    runs_assign_iff.mpr ⟨V, by simp [Expr.eval, c2s, hc1_st 95, h95], rfl, rfl, rfl⟩
  have rc4 : Runs w p ω (.assign 2 (.reg 67)) c3 .normal c4 2 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, c3, c2s, hc1_st 67, h67], rfl, rfl, rfl⟩
  have rc5 : Runs w p ω (.assign 3 (.reg 68)) c4 .normal c5 2 :=
    runs_assign_iff.mpr ⟨P, by simp [Expr.eval, c4, c3, c2s, hc1_st 68, h68], rfl, rfl, rfl⟩
  have rc6 : Runs w p ω (.assign 4 (.bin .add (.reg 97) (.const 16))) c5 .normal c6 4 :=
    runs_assign_iff.mpr ⟨root + 16, by
      simp [Expr.eval, BinOp.eval, c5, c4, c3, c2s, hc1_st 97, h97,
        show 16 < 2 ^ w by omega, show root + 16 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have rc7 : Runs w p ω (.assign 78 (.bin .add (.bin .mul (.const 20)
      (.bin .add (.bin .mul (.const 4) (.reg 67)) (.const 8))) (.const 100))) c6 .normal c7 10 :=
    runs_assign_iff.mpr ⟨sp, by
      simp [Expr.eval, BinOp.eval, c6, c5, c4, c3, c2s, hc1_st 67, h67, sp,
        show 4 < 2 ^ w by omega, show 8 < 2 ^ w by omega, show 20 < 2 ^ w by omega,
        show 100 < 2 ^ w by omega, show 4 * L < 2 ^ w by omega,
        show 4 * L + 8 < 2 ^ w by omega, show 20 * (4 * L + 8) < 2 ^ w by omega, hsearchW],
      rfl, rfl, rfl⟩
  have rc8 : Runs w p ω (.assign 79 (.reg 78)) c7 .normal c8 2 :=
    runs_assign_iff.mpr ⟨sp, by simp [Expr.eval, c7], rfl, rfl, rfl⟩
  obtain ⟨s2, rHdr, hs2_74, hs2_77, hchainH, hnumH, hframeH, hzH, hregsH, _⟩ :=
    allocateMinRatioInitHeader_runs (w := w) (heap := handle) (m := m) (V := V) (depth := d)
      (branch := branch) (psi := psi) (alphaPtr := root + 16) (quality := k) (epsilon := epsExp)
      (limbs := L) (precision := P) (searchSpace := sp) (readSpace := sp)
      (p := p) (ω := ω) (st := c8)
      (by simp [c8, c7, c6, c5, c4, c3, c2s, hc1_7, handle, table])
      (by simp [c8, c7, c6, c5, c4, c3, c2s])
      (by simp [c8, c7, c6, c5, c4, c3])
      (by simp [c8, c7, c6, c5, c4, c3, c2s, hc1_st 75, h75])
      (by simp [c8, c7, c6, c5, c4, c3, c2s, hc1_st 76, h76])
      (by simp [c8, c7, c6, c5, c4, c3, c2s, hc1_st 6, h6])
      (by simp [c8, c7, c6])
      (by simp [c8, c7, c6, c5, c4, c3, c2s, hc1_st 72, h72])
      (by simp [c8, c7, c6, c5, c4, c3, c2s, hc1_st 73, h73])
      (by simp [c8, c7, c6, c5, c4])
      (by simp [c8, c7, c6, c5])
      (by simp [c8, c7]) (by simp [c8])
      (fun a ha => by simpa [c8, c7, c6, c5, c4, c3, c2s, handle, table] using hzHandle a ha)
      (by omega)
  have rFull : Runs w p ω (initConcreteStage2 graphPack sortedEnds copy) st .normal s2
      (2 + (2 + (cPack + (2 + (2 + (2 + ((2 + cSort + 1) +
        (cMeta + (2 + (2 + (2 + (2 + (4 + (10 + (2 + 79 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)
        + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨p1, 2, _, rp1,
    runs_seq_iff.mpr (Or.inr ⟨p2, 2, _, rp2,
    runs_seq_iff.mpr (Or.inr ⟨p3, cPack, _, rPack,
    runs_seq_iff.mpr (Or.inr ⟨b1, 2, _, rb1,
    runs_seq_iff.mpr (Or.inr ⟨b2, 2, _, rb2,
    runs_seq_iff.mpr (Or.inr ⟨b9, 2, _, rb9,
    runs_seq_iff.mpr (Or.inr ⟨b10, 2 + cSort + 1, _, rb10,
    runs_seq_iff.mpr (Or.inr ⟨c1, cMeta, _, rcMeta,
    runs_seq_iff.mpr (Or.inr ⟨c2s, 2, _, rc2,
    runs_seq_iff.mpr (Or.inr ⟨c3, 2, _, rc3,
    runs_seq_iff.mpr (Or.inr ⟨c4, 2, _, rc4,
    runs_seq_iff.mpr (Or.inr ⟨c5, 2, _, rc5,
    runs_seq_iff.mpr (Or.inr ⟨c6, 4, _, rc6,
    runs_seq_iff.mpr (Or.inr ⟨c7, 10, _, rc7,
    runs_seq_iff.mpr (Or.inr ⟨c8, 2, 79, rc8, rHdr, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hkeepC1 (r : ℕ) (hr74 : r ≠ 74 := by decide) (hr77 : r ≠ 77 := by decide)
      (hr79 : r ≠ 79 := by decide) (hr78 : r ≠ 78 := by decide) (hr4 : r ≠ 4 := by decide)
      (hr3 : r ≠ 3 := by decide) (hr2 : r ≠ 2 := by decide) (hr1 : r ≠ 1 := by decide)
      (hr0 : r ≠ 0 := by decide) :
      s2.regs r = c1.regs r := by
    rw [hregsH r hr74 hr77]
    simp [c8, c7, c6, c5, c4, c3, c2s, Function.update_of_ne,
      hr79, hr78, hr4, hr3, hr2, hr1, hr0]
  have hkeepAll (r : ℕ) (hr74 : r ≠ 74 := by decide) (hr77 : r ≠ 77 := by decide)
      (hr79 : r ≠ 79 := by decide) (hr78 : r ≠ 78 := by decide) (hr4 : r ≠ 4 := by decide)
      (hr3 : r ≠ 3 := by decide) (hr2 : r ≠ 2 := by decide) (hr1 : r ≠ 1 := by decide)
      (hr0 : r ≠ 0 := by decide) (hr7 : r ≠ 7 := by decide) (hr10 : r ≠ 10 := by decide)
      (hr58 : r ≠ 58 := by decide) (hr59 : r ≠ 59 := by decide) (hr60 : r ≠ 60 := by decide) :
      s2.regs r = b10.regs r :=
    (hkeepC1 r hr74 hr77 hr79 hr78 hr4 hr3 hr2 hr1 hr0).trans
      (hc1_keep r hr0 hr7 hr10 hr58 hr59 hr60)
  have hmemBelowLen0 (a : ℕ) (ha : a < len0Buf) : s2.mem a = b10.mem a :=
    (hframeH a (by omega)).trans (hc1_frame a ha)
  have hDG2 : DynGraphAt s2.mem rootGraph G.n eCap G :=
    dynGraphAt_of_agree hDG3 (fun a _ hhi =>
      (hmemBelowLen0 a (by omega)).trans (hframeSort a (by omega)))
  refine ⟨s2, _, rFull,
    (hkeepAll 9).trans (by simp [b10, b9]),
    (hkeepAll 56).trans ((hb10_r 56).trans h56),
    (hkeepAll 57).trans ((hb10_r 57).trans h57),
    (hkeepC1 58).trans hc1_58,
    (hkeepC1 59).trans hc1_59,
    (hkeepC1 60).trans hc1_60,
    (hkeepAll 67).trans ((hb10_r 67).trans h67),
    (hkeepAll 68).trans ((hb10_r 68).trans h68),
    (hkeepAll 70).trans ((hb10_r 70).trans h70),
    (hkeepAll 71).trans ((hb10_r 71).trans h71),
    hs2_74,
    (hkeepAll 75).trans ((hb10_r 75).trans h75),
    (hkeepAll 76).trans ((hb10_r 76).trans h76),
    hs2_77,
    (hkeepAll 96).trans (by simp [b10, b9, b2, b1]),
    hDG2,
    fun i hi => (hmemBelowLen0 _ (by omega)).trans (hb10_MTab i hi),
    (hmemBelowLen0 _ (by omega)).trans ((hb10_mem_below _ (by omega)).trans hDepth),
    (hframeH _ (by unfold solverN0Addr; omega)).trans hc1_n0,
    fun i hi => (hframeH _ (by unfold solverLvlMAddr solverN0Addr; omega)).trans (hc1_lvlM i hi),
    (hframeH _ (by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega)).trans hc1_meta0,
    (hframeH _ (by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega)).trans hc1_metaG0,
    (hframeH _ (by unfold solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega)).trans hc1_sh,
    (hframeH _ (by unfold solverSelectBlocksAddr solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega)).trans hc1_sb,
    fun j hj => (hframeH _ (by
      have hmLLe : m * L ≤ eCap * L := Nat.mul_le_mul_right L hmLeECap; omega)).trans
      ((hc1_len0 j hj).trans (hb10_mem_below _ (by omega))),
    ?_, ?_, hchainH, hnumH,
    fun a ha => (hmemBelowLen0 a (by omega)).trans (hb10_mem_below a ha),
    hzH, by omega⟩
  · have hOrdAt' : OrdListAt sSort.mem ordBase (Bundle.sortedEnds G) (1 + 2 * G.n + 2 * m) := by
      simpa [hGm] using hOrdAt
    exact ordListAt_of_agree hOrdAt' (fun j hj => hmemBelowLen0 (ordBase + j) (by omega))
  · intro j hj
    rw [hmemBelowLen0 (ordBase + j) (by omega)]
    exact hOrdW j (by omega)

/-- Stage 2 with the depth store runs. The header holds the nine chain words, the last one being
the depth `coreDepth` that Stage 1 wrote at `pBase + 6 + d`. Register `98` keeps the depth for
the rebuilds of Stage 3. -/
theorem initConcreteStage2D_runs
    {w graphPack sortedEnds copy root pBase rootGraph graph gradient lengths m eCap V L P d
      branch psi k epsExp N₀ coreDepth : ℕ}
    {lvlM : ℕ → ℕ} {G : MGraph} {p : Program} {ω : ℕ → Bool} {st : State}
    (hpack : MeetsContract w p graphPack
      (dgInitFromListsContract w G.n eCap G (G.V.sort (· ≤ ·))
        ((G.E.sort (· ≤ ·)).map (fun e => (e, G.tail e, G.head e)))))
    (hsortAt : p.procs[sortedEnds]? = some buildSortedEndsBody)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h6 : st.regs 6 = psi) (h7 : st.regs 7 = rootGraph) (h56 : st.regs 56 = N₀)
    (h57 : st.regs 57 = pBase + 6) (h61 : st.regs 61 = eCap) (h67 : st.regs 67 = L)
    (h68 : st.regs 68 = P) (h69 : st.regs 69 = graph) (h70 : st.regs 70 = gradient)
    (h71 : st.regs 71 = lengths) (h72 : st.regs 72 = k) (h73 : st.regs 73 = epsExp)
    (h75 : st.regs 75 = d) (h76 : st.regs 76 = branch) (h93 : st.regs 93 = G.n)
    (h94 : st.regs 94 = m) (h95 : st.regs 95 = V) (h97 : st.regs 97 = root)
    (hG : GraphAt st.mem graph G) (hGV : G.IsValid) (hGm : G.m = m)
    (hVlt : ∀ v ∈ G.V, v < G.n) (hElt : ∀ e ∈ G.E, e < eCap) (hmLeECap : m ≤ eCap)
    (hGraphBelow : graph + (graphWords G).length ≤ root)
    (hLenBelow : lengths + m * L ≤ root)
    (hroot16 : root + 16 ≤ pBase)
    (hpBaseLe : pBase + 7 + d ≤ rootGraph)
    (hMTab : ∀ i < d, st.mem (pBase + 6 + i) = lvlM i)
    (hDepth : st.mem (pBase + 6 + d) = coreDepth)
    (hz : ZeroFrom st.mem rootGraph)
    (hNw : N₀ < 2 ^ w) (hdPos : 0 < d) (hsearchW : 20 * (4 * L + 8) + 100 < 2 ^ w)
    (hw17 : 17 < 2 ^ w)
    (hroom : rootGraph + dynGraphSize G.n eCap + (1 + 4 * G.n + 2 * eCap) + eCap * L +
      (4 * d + 4) + 18 < 2 ^ w) :
    let ordBase := rootGraph + dynGraphSize G.n eCap
    let len0Buf := ordBase + 1 + 4 * G.n + 2 * eCap
    let table := len0Buf + eCap * L
    let handle := solverHandleAddr table d
    ∃ s2 c2,
      Runs w p ω (initConcreteStage2D graphPack sortedEnds copy) st .normal s2 c2 ∧
      s2.regs 9 = ordBase ∧ s2.regs 56 = N₀ ∧ s2.regs 57 = pBase + 6 ∧
      s2.regs 58 = solverLevelMetaAddr table d ∧ s2.regs 59 = len0Buf ∧
      s2.regs 60 = solverLvlMAddr table d ∧
      s2.regs 67 = L ∧ s2.regs 68 = P ∧ s2.regs 70 = gradient ∧ s2.regs 71 = lengths ∧
      s2.regs 74 = handle ∧ s2.regs 75 = d ∧ s2.regs 76 = branch ∧
      s2.regs 77 = handle + 18 ∧ s2.regs 96 = rootGraph ∧ s2.regs 98 = coreDepth ∧
      DynGraphAt s2.mem rootGraph G.n eCap G ∧
      (∀ i < d, s2.mem (pBase + 6 + i) = lvlM i) ∧ s2.mem (pBase + 6 + d) = coreDepth ∧
      s2.mem (solverN0Addr table d) = N₀ ∧
      (∀ i < d, s2.mem (solverLvlMAddr table d + i) = lvlM i) ∧
      s2.mem (solverLevelMetaAddr table d) = len0Buf ∧
      s2.mem (solverLevelMetaAddr table d + d) = rootGraph ∧
      s2.mem (solverSelectHeapAddr table d) = 0 ∧
      s2.mem (solverSelectBlocksAddr table d) = 0 ∧
      (∀ j < m * L, s2.mem (len0Buf + j) = st.mem (lengths + j)) ∧
      OrdListAt s2.mem ordBase (Bundle.sortedEnds G) (1 + 2 * G.n + 2 * m) ∧
      (∀ j < 1 + 2 * G.n + 2 * m, s2.mem (ordBase + j) < 2 ^ w) ∧
      SolverChainHeaderAt s2.mem handle m V d branch psi (root + 16) k epsExp coreDepth ∧
      MinRatioNumericHeaderAt s2.mem handle L P (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
      (∀ a < rootGraph, s2.mem a = st.mem a) ∧
      ZeroFrom s2.mem (handle + 18) ∧
      c2 ≤ (130 * G.n + 490 * m) + (150 * eCap + 60 * G.n) + 30 * (m * L) + 30 * d + 610 := by
  intro ordBase len0Buf table handle
  have hhandleDef : handle = table + (4 * d + 4) := by
    unfold handle solverHandleAddr solverSelectBlocksAddr solverSelectHeapAddr
      solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega
  obtain ⟨s1, c1, hr1, h9, h56', h57', h58, h59, h60, h67', h68', h70', h71', h74, h75', h76',
    h77, h96', hDG1, hlvl, hdep, hn0, hlvlCopy, hmeta0, hmetaG0, hsh, hsb, hlenCopy, hordAt, hordW,
    hchain, hnum, hframe, hzero, hc1⟩ :=
    initConcreteStage2_runs (w := w) (ω := ω) hpack hsortAt hcopy
      h6 h7 h56 h57 h61 h67 h68 h69 h70 h71 h72 h73 h75 h76 h93 h94 h95 h97
      hG hGV hGm hVlt hElt hmLeECap hGraphBelow hLenBelow hroot16 hpBaseLe hMTab hDepth hz
      hNw hdPos hsearchW hw17 (by omega)
  have hsrcW : pBase + 6 + d < 2 ^ w := by omega
  obtain ⟨s2, hr2, hmem2, h98, h77', hregs2, _⟩ :=
    storeCoreDepthHeader_runs (w := w) (p := p) (ω := ω) (st := s1) (handle := handle)
      h74 h57' h75' hdep hsrcW (by omega)
  have hagree (a : ℕ) (ha : a ≠ handle + 17) : s2.mem a = s1.mem a := by
    rw [hmem2, Function.update_of_ne ha]
  have hk (r : ℕ) (h98' : r ≠ 98 := by decide) (h77'' : r ≠ 77 := by decide) :
      s2.regs r = s1.regs r := hregs2 r h98' h77''
  have hmLLe : m * L ≤ eCap * L := Nat.mul_le_mul_right L hmLeECap
  refine ⟨s2, c1 + 16 + 1, runs_seq_iff.mpr (Or.inr ⟨s1, c1, 16, hr1, hr2, rfl⟩),
    (hk 9).trans h9, (hk 56).trans h56', (hk 57).trans h57',
    (hk 58).trans h58, (hk 59).trans h59, (hk 60).trans h60,
    (hk 67).trans h67', (hk 68).trans h68', (hk 70).trans h70', (hk 71).trans h71',
    (hk 74).trans h74, (hk 75).trans h75', (hk 76).trans h76', h77', (hk 96).trans h96', h98,
    dynGraphAt_of_agree hDG1 (fun a _ hhi => hagree a (by omega)),
    fun i hi => (hagree _ (by omega)).trans (hlvl i hi),
    (hagree _ (by omega)).trans hdep,
    (hagree _ (by unfold solverN0Addr; omega)).trans hn0,
    fun i hi => (hagree _ (by unfold solverLvlMAddr solverN0Addr; omega)).trans (hlvlCopy i hi),
    (hagree _ (by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega)).trans hmeta0,
    (hagree _ (by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega)).trans hmetaG0,
    (hagree _ (by unfold solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega)).trans hsh,
    (hagree _ (by unfold solverSelectBlocksAddr solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega)).trans hsb,
    fun j hj => (hagree _ (by omega)).trans (hlenCopy j hj),
    ordListAt_of_agree hordAt (fun j hj => hagree (ordBase + j) (by omega)),
    fun j hj => by rw [hagree (ordBase + j) (by omega)]; exact hordW j hj,
    SolverChainHeaderAt.of_chain (ListAt.congr hchain fun a _ ha => hagree a (by simp at ha; omega))
      (by rw [hmem2]; simp),
    ListAt.congr hnum fun a _ ha => hagree a (by simp at ha; omega),
    fun a ha => (hagree a (by omega)).trans (hframe a ha),
    fun a ha => by rw [hagree a (ne_of_gt ha)]; exact hzero a (Nat.le_trans (Nat.le_succ _) ha), by omega⟩

end MinCostFlow.MinRatio
