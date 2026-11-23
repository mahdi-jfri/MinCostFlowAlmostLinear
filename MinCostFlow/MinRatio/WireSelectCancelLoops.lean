module

public import MinCostFlow.MinRatio.WireSelectCancel
import WordRAM.Tactic

/-!
# Verification of `cancelPairInnerBody`, `cancelPairOuterBody`, and `cancelRoutePathsBody`

Completes the Word-RAM verification of the Algorithm 2 (page 29) path-cancellation post-processing
loop (`WireSelectQuery.lean`):
1. `cancelPairInner_runs`: verifies the inner `j .. K - 1` scan by induction on `K - j`.
2. `cancelPairOuter_runs`: verifies the outer `i .. K - 1` scan by induction on `K - i`.
3. `cancelRoutePaths_runs`: verifies the full `cancelRoutePathsBody` repeat-until-quiescent loop
   by induction on `4 * K^4 - steps` using `pathSwap_index_history`, matching
   `cancelRoutePathsSpace` and `cancelRoutePathsCost` (`WireSelectQuery.lean`) with zero footprint
   growth, and proving cancellation-freeness (`pathCancel_no_reverse_of_scan`) plus exact tree-flow
   preservation.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program LinkCut.PathProg

/-! ## 1. Inner scan `j .. K - 1` (`cancelPairInnerBody`) -/

theorem cancelPairInner_runs
    {w L P m V psi k epsExp drainUnit initTree cmpExch self
      root descBase pathsBase K i j flagPtr work size
      levelsEnd0 intCap0 handle0 treeHeap0 maxEdges maxPaths : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {opTree : ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {loc : SelectHeapLoc}
    {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {B R : ℤ} {pathsInit paths : List (ℕ × ℕ)}
    {route : ℕ → List (ℕ × ℕ)} {steps : ℕ}
    (hw16 : 16 < 2 ^ w)
    (hfmt4 : fmt.limbBits = 4)
    (hlocalCore : Rcore.Local)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hCmpExch : ∀ ab cd ad cb : ℤ,
      MeetsContract w p cmpExch (pathCompareExchangeContract w 4 ab cd ad cb))
    (hpSelf : p.procs[self]? = some (cancelPairInnerBody self (opTree 3) cmpExch))
    (hFsub : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E)
    (hlogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hmaxE1 : 1 ≤ maxEdges) (hmaxEP : 2 * maxEdges ≤ maxPaths)
    (hcapE : 2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ))
    (hcapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hlocEnd : loc.endAddr ≤ descBase)
    (h2nW : 2 * model.extG.n + 1 < 2 ^ w) (htreeHW : treeHeap0 < 2 ^ w)
    (hroom : work + (K - j) * (4 * pathApplySpace L + 2 * L) < 2 ^ w)
    (hij : i < j)
    (hS : CancelState P m V psi k epsExp drainUnit loc root descBase pathsBase K flagPtr size model B R pathsInit
      levelsEnd0 intCap0 handle0 treeHeap0 mem tok paths route steps work) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let F := model.chain.toTreeChain.chainTree
    let ℓint := fun ei => model.extℓ (model.intToExt ei)
    ∃ (work' cIn : ℕ) (st' : State) (tok' : SolverToken cfg L Rcore)
      (paths' : List (ℕ × ℕ)) (route' : ℕ → List (ℕ × ℕ)) (steps' : ℕ),
      Runs w p ω (cancelPairInnerBody self (opTree 3) cmpExch)
        (startState [treeHeap0, L, pathsBase, K, i, j, flagPtr, work] mem pos)
        (.returned work') st' cIn ∧
      work ≤ work' ∧ work' ≤ work + (K - j) * (4 * pathApplySpace L + 2 * L) ∧
      CancelState P m V psi k epsExp drainUnit loc root descBase pathsBase K flagPtr size model B R pathsInit
        levelsEnd0 intCap0 handle0 treeHeap0 st'.mem tok' paths' route' steps' work' ∧
      PreservesLevelMeta tok tok' mem st'.mem ∧
      (∀ x < flagPtr, (x < pathsBase ∨ pathsBase + 2 * K ≤ x) →
        ¬ Rrep.foot root tok x → st'.mem x = mem x) ∧
      (∀ x, Rrep.foot root tok' x → Rrep.foot root tok x) ∧
      steps ≤ steps' ∧
      (st'.mem flagPtr = 0 →
        mem flagPtr = 0 ∧ paths' = paths ∧ route' = route ∧ steps' = steps ∧
        ∀ j', (hjj' : j ≤ j') → ∀ (hj' : j' < paths.length),
          let hi : i < paths.length := (lt_of_lt_of_le hij hjj').trans hj'
          walkLength ℓint (F.forestPath (paths[i]'hi).1 (paths[i]'hi).2) +
            walkLength ℓint (F.forestPath (paths[j']'hj').1 (paths[j']'hj').2) ≤
          walkLength ℓint (F.forestPath (paths[i]'hi).1 (paths[j']'hj').2) +
            walkLength ℓint (F.forestPath (paths[j']'hj').1 (paths[i]'hi).2)) ∧
      (st'.mem flagPtr ≠ 0 → mem flagPtr ≠ 0 ∨ steps < steps') ∧
      cIn + Rrep.phi root tok' st'.mem ≤
        (K - j) * (4 * pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 117 * L + 390) + 10 +
          Rrep.phi root tok mem := by
  dsimp only
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  let F := model.chain.toTreeChain.chainTree
  let ℓint := fun ei => model.extℓ (model.intToExt ei)
  induction hrem : K - j generalizing j work mem pos tok paths route steps with
  | zero =>
    have hge : ¬ j < K := by omega
    have hRun : Runs w p ω (cancelPairInnerBody self (opTree 3) cmpExch)
        (startState [treeHeap0, L, pathsBase, K, i, j, flagPtr, work] mem pos)
        (.returned work) (startState [treeHeap0, L, pathsBase, K, i, j, flagPtr, work] mem pos) 6 := by
      unfold cancelPairInnerBody
      refine runs_cond_iff.mpr ⟨0, 2, ?_, ?_, by simp [Expr.size]⟩
      · simp [Expr.eval, BinOp.eval, startState, hge]
      · simp [runs_ret_iff, Expr.eval, startState]
    refine ⟨work, 6, _, tok, paths, route, steps, hRun, le_rfl, by simp, hS,
      PreservesLevelMeta.refl tok mem, fun _ _ _ _ => rfl, fun _ h => h, le_rfl, ?_, fun h => Or.inl h,
      by rw [Nat.zero_mul, Nat.zero_add]; exact Nat.add_le_add_right (by decide) _⟩
    intro h0
    refine ⟨h0, rfl, rfl, rfl, fun j' hjj' hj' => ?_⟩
    have := hS.hlen; omega
  | succ rem ih =>
    rw [hrem] at hroom
    have hj : j < K := by omega
    have hrem' : K - (j + 1) = rem := by omega
    have hStepRoom : work + (4 * pathApplySpace L + 2 * L) < 2 ^ w := by
      have : 1 * (4 * pathApplySpace L + 2 * L) ≤ (rem + 1) * (4 * pathApplySpace L + 2 * L) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    obtain ⟨w1, cStep, st1, tok1, paths1, route1, steps1, hRunStep,
        hr1_0, hr1_1, hr1_2, hr1_3, hr1_4, hr1_5, hr1_6, hr1_7,
        hw1Lo, hw1Hi, hS1, hmeta1, hfr1, hft1, hOut1, hcStep⟩ :=
      cancelPairStep_runs hw16 hfmt4 hlocalCore hTreeImpl hCmpExch hFsub hlogW hmaxE1 hmaxEP
        hcapE hcapT hlocEnd h2nW htreeHW hStepRoom hij hj hS
    have hRecRoom : w1 + (K - (j + 1)) * (4 * pathApplySpace L + 2 * L) < 2 ^ w := by
      rw [hrem']
      have hmul : (rem + 1) * (4 * pathApplySpace L + 2 * L) =
          (4 * pathApplySpace L + 2 * L) + rem * (4 * pathApplySpace L + 2 * L) := by ring
      omega
    obtain ⟨w2, cRec, st2, tok2, paths2, route2, steps2, hRunRec,
        hw2Lo, hw2Hi, hS2, hmeta2, hfr2, hft2, hSteps12, hZero2, hNz2, hcRec⟩ :=
      ih hRecRoom (by omega) hS1 hrem'
    -- Assemble `Runs` for `cancelPairInnerBody`
    have hj1W : j + 1 < 2 ^ w := by
      have := hS.hPtLt; have := hS.hFlagLt; omega
    let stC : State := ⟨st2.mem, Function.update st1.regs 17 w2, st2.pos⟩
    have hrCall : Runs w p ω
        (.call 17 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .bin .add (.reg 5) (.const 1), .reg 6, .reg 7])
        st1 .normal stC (cRec + 11) := by
      refine runs_call_iff.mpr ⟨[treeHeap0, L, pathsBase, K, i, j + 1, flagPtr, w1], _, .returned w2, st2, cRec,
        ?_, hpSelf, hRunRec, rfl, rfl, ?_⟩
      · simp [evalArgs, Expr.eval, BinOp.eval, hr1_0, hr1_1, hr1_2, hr1_3, hr1_4, hr1_5, hr1_6, hr1_7,
          show 1 < 2 ^ w by omega, hj1W]
      · simp [argsSize, Expr.size]; omega
    have hrRet : Runs w p ω (.ret (.reg 17)) stC (.returned w2) stC 2 :=
      runs_ret_iff.mpr ⟨w2, by simp [Expr.eval, stC], rfl, rfl, rfl⟩
    have hrTail : Runs w p ω
        (.call 17 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .bin .add (.reg 5) (.const 1), .reg 6, .reg 7] ;;
         .ret (.reg 17))
        st1 (.returned w2) stC (cRec + 11 + 2 + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨stC, cRec + 11, 2, hrCall, hrRet, rfl⟩)
    have hrThen := runs_appendStmt hRunStep hrTail
    have hRunFull : Runs w p ω (cancelPairInnerBody self (opTree 3) cmpExch)
        (startState [treeHeap0, L, pathsBase, K, i, j, flagPtr, work] mem pos)
        (.returned w2) stC (1 + 3 + (cStep + (cRec + 11 + 2 + 1) + 1)) := by
      unfold cancelPairInnerBody
      refine runs_cond_iff.mpr ⟨1, cStep + (cRec + 11 + 2 + 1) + 1, ?_, ?_, by simp [Expr.size]; omega⟩
      · simp [Expr.eval, BinOp.eval, startState, hj, show 1 < 2 ^ w by omega]
      · dsimp only [appendStmt] at hrThen; exact hrThen
    have hfr02 : ∀ x < flagPtr, (x < pathsBase ∨ pathsBase + 2 * K ≤ x) →
        ¬ Rrep.foot root tok x → st2.mem x = mem x := fun x hx hOut hnf =>
      (hfr2 x hx hOut (fun hf => hnf (hft1 x hf))).trans (hfr1 x hx hOut hnf)
    have hft02 : ∀ x, Rrep.foot root tok2 x → Rrep.foot root tok x := fun x hf => hft1 x (hft2 x hf)
    have hSpace02 : w2 ≤ work + (rem + 1) * (4 * pathApplySpace L + 2 * L) := by
      have hmul : (rem + 1) * (4 * pathApplySpace L + 2 * L) =
          (4 * pathApplySpace L + 2 * L) + rem * (4 * pathApplySpace L + 2 * L) := by ring
      omega
    have hCost02 : (1 + 3 + (cStep + (cRec + 11 + 2 + 1) + 1)) + Rrep.phi root tok2 st2.mem ≤
        (rem + 1) * (4 * pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 117 * L + 390) + 10 +
          Rrep.phi root tok mem := by
      have hmul : (rem + 1) * (4 * pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 117 * L + 390) =
          (4 * pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 117 * L + 390) +
            rem * (4 * pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 117 * L + 390) := by ring
      dsimp only [Rrep] at hcStep hcRec ⊢
      omega
    have hSteps02 : steps ≤ steps2 := by
      rcases hOut1 with ⟨_, _, hst1⟩ | ⟨_, _, _, _, hst1⟩ <;> omega
    have hZero02 : st2.mem flagPtr = 0 →
        mem flagPtr = 0 ∧ paths2 = paths ∧ route2 = route ∧ steps2 = steps ∧
        ∀ j', (hjj' : j ≤ j') → ∀ (hj' : j' < paths.length),
          let hi : i < paths.length := (lt_of_lt_of_le hij hjj').trans hj'
          walkLength ℓint (F.forestPath (paths[i]'hi).1 (paths[i]'hi).2) +
            walkLength ℓint (F.forestPath (paths[j']'hj').1 (paths[j']'hj').2) ≤
          walkLength ℓint (F.forestPath (paths[i]'hi).1 (paths[j']'hj').2) +
            walkLength ℓint (F.forestPath (paths[j']'hj').1 (paths[i]'hi).2) := by
      intro hFl0
      obtain ⟨hFl1, hp21, hr21, hs21, hScan2⟩ := hZero2 hFl0
      rcases hOut1 with ⟨_, hFl1', _⟩ | ⟨hLeIJ, hFl1', hp1, hr1, hs1⟩
      · omega
      · refine ⟨hFl1'.symm.trans hFl1, hp21.trans hp1, hr21.trans hr1, hs21.trans hs1, ?_⟩
        intro j' hjj' hj'
        by_cases hjeq : j' = j
        · subst hjeq; exact hLeIJ
        · have hj1' : j + 1 ≤ j' := by omega
          simpa [hp1] using hScan2 j' hj1' (by rw [hp1]; exact hj')
    have hNz02 : st2.mem flagPtr ≠ 0 → mem flagPtr ≠ 0 ∨ steps < steps2 := by
      intro hFlNz
      rcases hOut1 with ⟨_, _, hs1⟩ | ⟨_, hFl1', _, _, hs1⟩
      · exact Or.inr (by omega)
      · rcases hNz2 hFlNz with h1 | hlt
        · exact Or.inl (hFl1' ▸ h1)
        · exact Or.inr (by omega)
    exact ⟨w2, _, stC, tok2, paths2, route2, steps2, hRunFull, le_trans hw1Lo hw2Lo,
      hSpace02, hS2, hmeta1.trans hmeta2, hfr02, hft02, hSteps02, hZero02, hNz02, hCost02⟩

/-! ## 2. Outer scan `i .. K - 1` (`cancelPairOuterBody`) -/

theorem cancelPairOuter_runs
    {w L P m V psi k epsExp drainUnit initTree cmpExch self inner
      root descBase pathsBase K i flagPtr work size
      levelsEnd0 intCap0 handle0 treeHeap0 maxEdges maxPaths : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {opTree : ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {loc : SelectHeapLoc}
    {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {B R : ℤ} {pathsInit paths : List (ℕ × ℕ)}
    {route : ℕ → List (ℕ × ℕ)} {steps : ℕ}
    (hw16 : 16 < 2 ^ w)
    (hfmt4 : fmt.limbBits = 4)
    (hlocalCore : Rcore.Local)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hCmpExch : ∀ ab cd ad cb : ℤ,
      MeetsContract w p cmpExch (pathCompareExchangeContract w 4 ab cd ad cb))
    (hpSelf : p.procs[self]? = some (cancelPairOuterBody self inner))
    (hpInner : p.procs[inner]? = some (cancelPairInnerBody inner (opTree 3) cmpExch))
    (hFsub : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E)
    (hlogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hmaxE1 : 1 ≤ maxEdges) (hmaxEP : 2 * maxEdges ≤ maxPaths)
    (hcapE : 2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ))
    (hcapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hlocEnd : loc.endAddr ≤ descBase)
    (h2nW : 2 * model.extG.n + 1 < 2 ^ w) (htreeHW : treeHeap0 < 2 ^ w)
    (hroom : work + (K - i) * K * (4 * pathApplySpace L + 2 * L) < 2 ^ w)
    (hS : CancelState P m V psi k epsExp drainUnit loc root descBase pathsBase K flagPtr size model B R pathsInit
      levelsEnd0 intCap0 handle0 treeHeap0 mem tok paths route steps work) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let F := model.chain.toTreeChain.chainTree
    let ℓint := fun ei => model.extℓ (model.intToExt ei)
    ∃ (work' cOut : ℕ) (st' : State) (tok' : SolverToken cfg L Rcore)
      (paths' : List (ℕ × ℕ)) (route' : ℕ → List (ℕ × ℕ)) (steps' : ℕ),
      Runs w p ω (cancelPairOuterBody self inner)
        (startState [treeHeap0, L, pathsBase, K, i, flagPtr, work] mem pos)
        (.returned work') st' cOut ∧
      work ≤ work' ∧ work' ≤ work + (K - i) * K * (4 * pathApplySpace L + 2 * L) ∧
      CancelState P m V psi k epsExp drainUnit loc root descBase pathsBase K flagPtr size model B R pathsInit
        levelsEnd0 intCap0 handle0 treeHeap0 st'.mem tok' paths' route' steps' work' ∧
      PreservesLevelMeta tok tok' mem st'.mem ∧
      (∀ x < flagPtr, (x < pathsBase ∨ pathsBase + 2 * K ≤ x) →
        ¬ Rrep.foot root tok x → st'.mem x = mem x) ∧
      (∀ x, Rrep.foot root tok' x → Rrep.foot root tok x) ∧
      steps ≤ steps' ∧
      (st'.mem flagPtr = 0 →
        mem flagPtr = 0 ∧ paths' = paths ∧ route' = route ∧ steps' = steps ∧
        ∀ i' j', i ≤ i' → (hij' : i' < j') → ∀ (hj' : j' < paths.length),
          let hi' : i' < paths.length := hij'.trans hj'
          walkLength ℓint (F.forestPath (paths[i']'hi').1 (paths[i']'hi').2) +
            walkLength ℓint (F.forestPath (paths[j']'hj').1 (paths[j']'hj').2) ≤
          walkLength ℓint (F.forestPath (paths[i']'hi').1 (paths[j']'hj').2) +
            walkLength ℓint (F.forestPath (paths[j']'hj').1 (paths[i']'hi').2)) ∧
      (st'.mem flagPtr ≠ 0 → mem flagPtr ≠ 0 ∨ steps < steps') ∧
      cOut + Rrep.phi root tok' st'.mem ≤
        (K - i) * K * (4 * pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 117 * L + 440) + 20 +
          Rrep.phi root tok mem := by
  dsimp only
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  let F := model.chain.toTreeChain.chainTree
  let ℓint := fun ei => model.extℓ (model.intToExt ei)
  induction hrem : K - i generalizing i work mem pos tok paths route steps with
  | zero =>
    have hge : ¬ i < K := by omega
    have hRun : Runs w p ω (cancelPairOuterBody self inner)
        (startState [treeHeap0, L, pathsBase, K, i, flagPtr, work] mem pos)
        (.returned work) (startState [treeHeap0, L, pathsBase, K, i, flagPtr, work] mem pos) 6 := by
      unfold cancelPairOuterBody
      refine runs_cond_iff.mpr ⟨0, 2, ?_, ?_, by simp [Expr.size]⟩
      · simp [Expr.eval, BinOp.eval, startState, hge]
      · simp [runs_ret_iff, Expr.eval, startState]
    refine ⟨work, 6, _, tok, paths, route, steps, hRun, le_rfl, by simp, hS,
      PreservesLevelMeta.refl tok mem, fun _ _ _ _ => rfl, fun _ h => h, le_rfl, ?_, fun h => Or.inl h,
      by rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_add]; exact Nat.add_le_add_right (by decide) _⟩
    intro h0
    refine ⟨h0, rfl, rfl, rfl, fun i' j' hii' hij' hj' => ?_⟩
    have := hS.hlen; omega
  | succ rem ih =>
    rw [hrem] at hroom
    have hi : i < K := by omega
    have hKpos : 1 ≤ K := by omega
    have hrem' : K - (i + 1) = rem := by omega
    set S := 4 * pathApplySpace L + 2 * L
    have hInLeK : (K - (i + 1)) * S ≤ K * S := Nat.mul_le_mul_right S (by omega)
    have hSplitS : (rem + 1) * K * S = K * S + rem * K * S := by ring
    have hInRoom : work + (K - (i + 1)) * S < 2 ^ w := by omega
    obtain ⟨w1, cIn, st1, tok1, paths1, route1, steps1, hRunIn,
        hw1Lo, hw1Hi, hS1, hmeta1, hfr1, hft1, hSteps01, hZero1, hNz1, hcIn⟩ :=
      cancelPairInner_runs hw16 hfmt4 hlocalCore hTreeImpl hCmpExch hpInner hFsub hlogW hmaxE1 hmaxEP
        hcapE hcapT hlocEnd h2nW htreeHW hInRoom (Nat.lt_succ_self i) hS
    change w1 ≤ work + (K - (i + 1)) * S at hw1Hi
    have hRecRoom : w1 + (K - (i + 1)) * K * S < 2 ^ w := by
      rw [hrem']; omega
    obtain ⟨w2, cRec, st2, tok2, paths2, route2, steps2, hRunRec,
        hw2Lo, hw2Hi, hS2, hmeta2, hfr2, hft2, hSteps12, hZero2, hNz2, hcRec⟩ :=
      ih hRecRoom hS1 hrem'
    change w2 ≤ w1 + rem * K * S at hw2Hi
    have hi1W : i + 1 < 2 ^ w := by
      have := hS.hPtLt; have := hS.hFlagLt; omega
    let s0 := startState [treeHeap0, L, pathsBase, K, i, flagPtr, work] mem pos
    let s1 : State := ⟨st1.mem, Function.update s0.regs 7 w1, st1.pos⟩
    let s2 : State := ⟨st2.mem, Function.update s1.regs 8 w2, st2.pos⟩
    have hrCallIn : Runs w p ω
        (.call 7 inner [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .bin .add (.reg 4) (.const 1), .reg 5, .reg 6])
        s0 .normal s1 (cIn + 11) := by
      refine runs_call_iff.mpr ⟨[treeHeap0, L, pathsBase, K, i, i + 1, flagPtr, work], _, .returned w1, st1, cIn,
        ?_, hpInner, hRunIn, rfl, rfl, ?_⟩
      · simp [evalArgs, Expr.eval, BinOp.eval, s0, startState, show 1 < 2 ^ w by omega, hi1W]
      · simp [argsSize, Expr.size]; omega
    have hrCallRec : Runs w p ω
        (.call 8 self [.reg 0, .reg 1, .reg 2, .reg 3, .bin .add (.reg 4) (.const 1), .reg 5, .reg 7])
        s1 .normal s2 (cRec + 10) := by
      refine runs_call_iff.mpr ⟨[treeHeap0, L, pathsBase, K, i + 1, flagPtr, w1], _, .returned w2, st2, cRec,
        ?_, hpSelf, hRunRec, rfl, rfl, ?_⟩
      · simp [evalArgs, Expr.eval, BinOp.eval, s1, s0, startState, show 1 < 2 ^ w by omega, hi1W]
      · simp [argsSize, Expr.size]; omega
    have hrRet : Runs w p ω (.ret (.reg 8)) s2 (.returned w2) s2 2 :=
      runs_ret_iff.mpr ⟨w2, by simp [Expr.eval, s2], rfl, rfl, rfl⟩
    have hRunFull : Runs w p ω (cancelPairOuterBody self inner)
        s0 (.returned w2) s2 (1 + 3 + ((cIn + 11) + ((cRec + 10) + 2 + 1) + 1)) := by
      unfold cancelPairOuterBody
      refine runs_cond_iff.mpr ⟨1, (cIn + 11) + ((cRec + 10) + 2 + 1) + 1, ?_, ?_, by simp [Expr.size]; omega⟩
      · simp [Expr.eval, BinOp.eval, s0, startState, hi, show 1 < 2 ^ w by omega]
      · exact runs_seq_iff.mpr (Or.inr ⟨s1, cIn + 11, (cRec + 10) + 2 + 1, hrCallIn,
          runs_seq_iff.mpr (Or.inr ⟨s2, cRec + 10, 2, hrCallRec, hrRet, rfl⟩), rfl⟩)
    have hfr02 : ∀ x < flagPtr, (x < pathsBase ∨ pathsBase + 2 * K ≤ x) →
        ¬ Rrep.foot root tok x → st2.mem x = mem x := fun x hx hOut hnf =>
      (hfr2 x hx hOut (fun hf => hnf (hft1 x hf))).trans (hfr1 x hx hOut hnf)
    have hft02 : ∀ x, Rrep.foot root tok2 x → Rrep.foot root tok x := fun x hf => hft1 x (hft2 x hf)
    have hSpace02 : w2 ≤ work + (rem + 1) * K * S := by omega
    have hCost02 : (1 + 3 + ((cIn + 11) + ((cRec + 10) + 2 + 1) + 1)) + Rrep.phi root tok2 st2.mem ≤
        (rem + 1) * K * (4 * pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 117 * L + 440) + 20 +
          Rrep.phi root tok mem := by
      set B0 := 4 * pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 117 * L
      have hStepIn : (K - (i + 1)) * (B0 + 390) + 39 ≤ K * (B0 + 440) :=
        calc (K - (i + 1)) * (B0 + 390) + 39
          _ ≤ K * (B0 + 390) + K * 50 :=
              Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (by omega)
          _ = K * (B0 + 440) := by ring
      have hMul : (rem + 1) * K * (B0 + 440) = K * (B0 + 440) + rem * K * (B0 + 440) := by ring
      dsimp only [Rrep] at hcIn hcRec ⊢
      omega
    have hZero02 : st2.mem flagPtr = 0 →
        mem flagPtr = 0 ∧ paths2 = paths ∧ route2 = route ∧ steps2 = steps ∧
        ∀ i' j', i ≤ i' → (hij' : i' < j') → ∀ (hj' : j' < paths.length),
          let hi' : i' < paths.length := hij'.trans hj'
          walkLength ℓint (F.forestPath (paths[i']'hi').1 (paths[i']'hi').2) +
            walkLength ℓint (F.forestPath (paths[j']'hj').1 (paths[j']'hj').2) ≤
          walkLength ℓint (F.forestPath (paths[i']'hi').1 (paths[j']'hj').2) +
            walkLength ℓint (F.forestPath (paths[j']'hj').1 (paths[i']'hi').2) := by
      intro hFl0
      obtain ⟨hFl1, hp21, hr21, hs21, hScan2⟩ := hZero2 hFl0
      obtain ⟨hFl0', hp10, hr10, hs10, hScan1⟩ := hZero1 hFl1
      refine ⟨hFl0', hp21.trans hp10, hr21.trans hr10, hs21.trans hs10, ?_⟩
      intro i' j' hii' hij' hj'
      by_cases hieq : i' = i
      · subst hieq; exact hScan1 j' (by omega) hj'
      · simpa [hp10] using hScan2 i' j' (by omega) hij' (by rw [hp10]; exact hj')
    have hNz02 : st2.mem flagPtr ≠ 0 → mem flagPtr ≠ 0 ∨ steps < steps2 := by
      intro hFlNz
      rcases hNz2 hFlNz with hFl1Nz | hlt12
      · rcases hNz1 hFl1Nz with h0 | hlt01
        · exact Or.inl h0
        · exact Or.inr (by omega)
      · exact Or.inr (by omega)
    exact ⟨w2, _, s2, tok2, paths2, route2, steps2, hRunFull, le_trans hw1Lo hw2Lo,
      hSpace02, hS2, hmeta1.trans hmeta2, hfr02, hft02, le_trans hSteps01 hSteps12, hZero02, hNz02, hCost02⟩

/-! ## 3. Full cancellation loop (`cancelRoutePathsBody`) -/

private theorem cancelRoutePaths_runs_aux
    {w L P m V psi k epsExp drainUnit initTree cmpExch self outer inner
      root descBase pathsBase K size
      levelsEnd0 intCap0 handle0 treeHeap0 maxEdges maxPaths : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {opTree : ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {loc : SelectHeapLoc}
    {ω : ℕ → Bool} {model : Alg2State cfg} {B R : ℤ} {pathsInit : List (ℕ × ℕ)}
    (hw16 : 16 < 2 ^ w)
    (hfmt4 : fmt.limbBits = 4)
    (hlocalCore : Rcore.Local)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hCmpExch : ∀ ab cd ad cb : ℤ,
      MeetsContract w p cmpExch (pathCompareExchangeContract w 4 ab cd ad cb))
    (hpSelf : p.procs[self]? = some (cancelRoutePathsBody self outer))
    (hpOuter : p.procs[outer]? = some (cancelPairOuterBody outer inner))
    (hpInner : p.procs[inner]? = some (cancelPairInnerBody inner (opTree 3) cmpExch))
    (hFforest : model.chain.toTreeChain.chainTree.IsForest)
    (hFsub : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E)
    (hℓpos : ∀ e ∈ model.chain.toTreeChain.chainTree.E, 0 < model.extℓ (model.intToExt e))
    (hInitLen : pathsInit.length = K)
    (hInitConn : ∀ p ∈ pathsInit, model.chain.toTreeChain.chainTree.Connected p.1 p.2)
    (hlogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hmaxE1 : 1 ≤ maxEdges) (hmaxEP : 2 * maxEdges ≤ maxPaths)
    (hcapE : 2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ))
    (hcapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hlocEnd : loc.endAddr ≤ descBase)
    (h2nW : 2 * model.extG.n + 1 < 2 ^ w)
    (rem : ℕ) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let F := model.chain.toTreeChain.chainTree
    let ℓint := fun ei => model.extℓ (model.intToExt ei)
    ∀ {workHeap pos steps : ℕ} {mem : ℕ → ℕ} {tok : SolverToken cfg L Rcore}
      {paths : List (ℕ × ℕ)} {route : ℕ → List (ℕ × ℕ)},
      4 * K ^ 4 - steps ≤ rem →
      Rrep.rep root model tok mem →
      SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      OffTreeRecBound model L mem tok.edgeRecords B →
      PathEndpointsAt mem pathsBase paths →
      paths.length = K →
      (∀ q ∈ paths, q.1 < model.extG.n ∧ q.2 < model.extG.n ∧ F.Connected q.1 q.2) →
      (∀ p ∈ paths, ∀ q ∈ paths, F.Connected p.1 q.1) →
      ValidSwapSeq F ℓint route steps →
      route 0 = pathsInit →
      route steps = paths →
      tok.levelsEnd = levelsEnd0 →
      tok.intCap = intCap0 →
      tok.handle = handle0 →
      tok.treeHeap = treeHeap0 →
      (∀ x < 2 * K, ¬ Rrep.foot root tok (pathsBase + x)) →
      (∀ a, loc.hb ≤ a → a < loc.endAddr → ¬ Rrep.foot root tok a) →
      (∀ a, tok.tag a = 18 → a < descBase) →
      (∀ a, Rrep.foot root tok a → a < workHeap) →
      ZeroFrom mem workHeap →
      pathsBase + 2 * K ≤ workHeap →
      descBase ≤ pathsBase →
      workHeap + (rem + 1) * (K * K * (4 * pathApplySpace L + 2 * L) + 1) < 2 ^ w →
      ∃ (work' cTot : ℕ) (st' : State) (tok' : SolverToken cfg L Rcore) (paths' : List (ℕ × ℕ)),
        Runs w p ω (cancelRoutePathsBody self outer)
          (startState [root, pathsBase, K, workHeap] mem pos) (.returned work') st' cTot ∧
        workHeap ≤ work' ∧
        work' ≤ workHeap + (rem + 1) * (K * K * (4 * pathApplySpace L + 2 * L) + 1) ∧
        tok'.levelsEnd = levelsEnd0 ∧ tok'.intCap = intCap0 ∧
        Rrep.rep root model tok' st'.mem ∧ PreservesLevelMeta tok tok' mem st'.mem ∧
        SelectHeapMatchesChain st'.mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model L st'.mem tok'.edgeRecords B ∧
        OffTreeRecBound model L st'.mem tok'.edgeRecords B ∧
        PathEndpointsAt st'.mem pathsBase paths' ∧
        paths'.length = K ∧
        (∀ q ∈ paths', q.1 < model.extG.n ∧ q.2 < model.extG.n ∧ F.Connected q.1 q.2) ∧
        (∀ e, (paths'.map fun q => walkFlow (F.forestPath q.1 q.2) e).sum =
          (pathsInit.map fun q => walkFlow (F.forestPath q.1 q.2) e).sum) ∧
        (∀ (x : ℕ × Bool) p q, p ∈ paths' → q ∈ paths' → x ∈ F.forestPath p.1 p.2 →
          (x.1, !x.2) ∉ F.forestPath q.1 q.2) ∧
        (∀ a, tok'.tag a = 18 → a < descBase) ∧
        ZeroFrom st'.mem work' ∧
        (∀ x < workHeap, (x < pathsBase ∨ pathsBase + 2 * K ≤ x) →
          ¬ Rrep.foot root tok x → st'.mem x = mem x) ∧
        (∀ x, Rrep.foot root tok' x → Rrep.foot root tok x) ∧
        cTot + Rrep.phi root tok' st'.mem ≤
          (rem + 1) * (K * K * (4 * pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 117 * L + 440) + 120) + 40 +
            Rrep.phi root tok mem := by
  dsimp only
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  let F := model.chain.toTreeChain.chainTree
  let ℓint := fun ei => model.extℓ (model.intToExt ei)
  have hPass : ∀ {workHeap pos steps : ℕ} {mem : ℕ → ℕ} {tok : SolverToken cfg L Rcore}
      {paths : List (ℕ × ℕ)} {route : ℕ → List (ℕ × ℕ)},
      Rrep.rep root model tok mem →
      SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      OffTreeRecBound model L mem tok.edgeRecords B →
      PathEndpointsAt mem pathsBase paths →
      paths.length = K →
      (∀ q ∈ paths, q.1 < model.extG.n ∧ q.2 < model.extG.n ∧ F.Connected q.1 q.2) →
      (∀ p ∈ paths, ∀ q ∈ paths, F.Connected p.1 q.1) →
      ValidSwapSeq F ℓint route steps →
      route 0 = pathsInit → route steps = paths →
      tok.levelsEnd = levelsEnd0 → tok.intCap = intCap0 →
      tok.handle = handle0 → tok.treeHeap = treeHeap0 →
      (∀ x < 2 * K, ¬ Rrep.foot root tok (pathsBase + x)) →
      (∀ a, loc.hb ≤ a → a < loc.endAddr → ¬ Rrep.foot root tok a) →
      (∀ a, tok.tag a = 18 → a < descBase) →
      (∀ a, Rrep.foot root tok a → a < workHeap) →
      ZeroFrom mem workHeap → pathsBase + 2 * K ≤ workHeap → descBase ≤ pathsBase →
      workHeap + (K * K * (4 * pathApplySpace L + 2 * L) + 1) < 2 ^ w →
      ∃ (w1 cPre cOut : ℕ) (st1 : State) (rg5 : ℕ → ℕ) (tok1 : SolverToken cfg L Rcore)
        (paths1 : List (ℕ × ℕ)) (route1 : ℕ → List (ℕ × ℕ)) (steps1 : ℕ),
        Runs w p ω
          (.assign 4 (.load (.reg 0)) ;; .assign 5 (.load (.reg 4)) ;;
           .assign 6 (.load (.bin .add (.reg 4) (.const 5))) ;;
           .store (.reg 3) (.const 0) ;;
           .call 7 outer [.reg 5, .reg 6, .reg 1, .reg 2, .const 0, .reg 3, .bin .add (.reg 3) (.const 1)] ;;
           .assign 8 (.load (.reg 3)))
          (startState [root, pathsBase, K, workHeap] mem pos) .normal ⟨st1.mem, rg5, st1.pos⟩ cPre ∧
        cPre = cOut + 32 ∧
        rg5 0 = root ∧ rg5 1 = pathsBase ∧ rg5 2 = K ∧ rg5 7 = w1 ∧ rg5 8 = st1.mem workHeap ∧
        workHeap + 1 ≤ w1 ∧ w1 ≤ workHeap + (K * K * (4 * pathApplySpace L + 2 * L) + 1) ∧
        CancelState P m V psi k epsExp drainUnit loc root descBase pathsBase K workHeap size model B R pathsInit
          levelsEnd0 intCap0 handle0 treeHeap0 st1.mem tok1 paths1 route1 steps1 w1 ∧
        steps1 ≤ 4 * K ^ 4 ∧ PreservesLevelMeta tok tok1 mem st1.mem ∧
        (∀ x < workHeap, (x < pathsBase ∨ pathsBase + 2 * K ≤ x) →
          ¬ Rrep.foot root tok x → st1.mem x = mem x) ∧
        (∀ x, Rrep.foot root tok1 x → Rrep.foot root tok x) ∧
        (st1.mem workHeap = 0 →
          (∀ e, (paths1.map fun q => walkFlow (F.forestPath q.1 q.2) e).sum =
            (pathsInit.map fun q => walkFlow (F.forestPath q.1 q.2) e).sum) ∧
          (∀ (x : ℕ × Bool) p q, p ∈ paths1 → q ∈ paths1 → x ∈ F.forestPath p.1 p.2 →
            (x.1, !x.2) ∉ F.forestPath q.1 q.2)) ∧
        (st1.mem workHeap ≠ 0 → steps < steps1) ∧
        cOut + Rrep.phi root tok1 st1.mem ≤
          K * K * (4 * pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 117 * L + 440) + 20 +
            Rrep.phi root tok mem := by
    intro workHeap pos steps mem tok paths route
      hrep hMatch hnum hoff hBd hPtAt hlen hPtOk hSame hHist hR0 hRt
      hlev hcap hhdl htreeH hnfPt hlocDisj htag18 hbelow hz hPtLt hDescLtPt hroom1
    have hrep0 := hrep
    obtain ⟨hrootDir, hdetect, hnumHdr, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags⟩ := hrep0
    obtain ⟨hOwn, _, t2, _⟩ := htags
    have hmemRoot : mem root = handle0 := hhdl ▸ (by simpa using hrootDir 0 (by simp))
    have hmemHdl : mem handle0 = treeHeap0 := htreeH ▸ hhdl ▸ (by simpa using hdetect 0 (by simp))
    have hmemL : mem (handle0 + 5) = L := hhdl ▸ (by simpa [Nat.add_assoc] using hnumHdr 0 (by simp))
    have hHdl5W : handle0 + 5 < 2 ^ w := by
      have hf : Rrep.foot root tok (tok.handle + 5) := Or.inl (hOwn _ (by rw [t2 5 (by omega)]; decide))
      have := hbelow _ hf; omega
    have hTreeHW : treeHeap0 < 2 ^ w := by
      have hf : Rrep.foot root tok tok.treeHeap := by
        refine Or.inr (Or.inl ?_)
        dsimp only [LinkCut.PathProg.pathRep, LinkCut.PathProg.arenaEnd, LinkCut.PathProg.arenaNb]
        exact ⟨le_rfl, by omega⟩
      have := hbelow _ hf; omega
    have hS0 : CancelState P m V psi k epsExp drainUnit loc root descBase pathsBase K workHeap size model B R pathsInit
        levelsEnd0 intCap0 handle0 treeHeap0 mem tok paths route steps (workHeap + 1) :=
      { hrep := hrep, hMatch := hMatch, hnum := hnum, hoff := hoff, hBd := hBd,
        hPtAt := hPtAt, hlen := hlen, hPtOk := hPtOk, hSameComp := hSame,
        hHist := hHist, hR0 := hR0, hRt := hRt, hlev := hlev, hcap := hcap,
        hhdl := hhdl, htreeH := htreeH, hnfPt := hnfPt, hlocDisj := hlocDisj,
        htag18 := htag18, hbelow := fun a ha => lt_trans (hbelow a ha) (Nat.lt_succ_self _),
        hz := fun x hx => hz x (by omega),
        hFlagDisj := fun hf => by have := hbelow _ hf; omega,
        hFlagLt := Nat.lt_succ_self _, hPtLt := hPtLt, hDescLtPt := hDescLtPt }
    obtain ⟨w1, cOut, st1, tok1, paths1, route1, steps1, hRunOut,
        hw1Lo, hw1Hi, hS1, hmeta1, hfr1, hft1, _, hZero1, hNz1, hcOut⟩ :=
      cancelPairOuter_runs hw16 hfmt4 hlocalCore hTreeImpl hCmpExch hpOuter hpInner hFsub hlogW hmaxE1 hmaxEP
        hcapE hcapT hlocEnd h2nW hTreeHW
        (by show (workHeap + 1) + (K - 0) * K * (4 * pathApplySpace L + 2 * L) < 2 ^ w; rw [Nat.sub_zero]; omega) hS0
    have hHist1 := pathSwap_index_history hFforest ℓint hℓpos route1 steps1
      (hS1.hR0.symm ▸ hInitConn) hS1.hHist
    have hSt1Bd : steps1 ≤ 4 * K ^ 4 := by rw [hS1.hR0, hInitLen] at hHist1; exact hHist1.1
    let s0 := startState [root, pathsBase, K, workHeap] mem pos
    let rg1 := Function.update s0.regs 4 handle0
    let rg2 := Function.update rg1 5 treeHeap0
    let rg3 := Function.update rg2 6 L
    let rg4 := Function.update rg3 7 w1
    let rg5 := Function.update rg4 8 (st1.mem workHeap)
    have hUpd0 : Function.update mem workHeap 0 = mem := by
      ext x; by_cases hx : x = workHeap
      · subst hx; rw [Function.update_self, hz x le_rfl]
      · exact Function.update_of_ne hx ..
    have hrg2_4 : rg2 4 = handle0 := by simp [rg2, rg1]
    have r1 : Runs w p ω (.assign 4 (.load (.reg 0))) s0 .normal ⟨mem, rg1, pos⟩ 3 :=
      runs_assign_iff.mpr ⟨handle0, by simp [Expr.eval, s0, startState, hmemRoot], rfl, rfl, rfl⟩
    have r2 : Runs w p ω (.assign 5 (.load (.reg 4))) ⟨mem, rg1, pos⟩ .normal ⟨mem, rg2, pos⟩ 3 :=
      runs_assign_iff.mpr ⟨treeHeap0, by simp [Expr.eval, rg1, hmemHdl], rfl, rfl, rfl⟩
    have r3 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 4) (.const 5))))
        ⟨mem, rg2, pos⟩ .normal ⟨mem, rg3, pos⟩ 5 :=
      runs_assign_iff.mpr ⟨L, by simp [Expr.eval, BinOp.eval, hrg2_4, show 5 < 2 ^ w by omega, hHdl5W, hmemL], rfl, rfl, rfl⟩
    have r4 : Runs w p ω (.store (.reg 3) (.const 0)) ⟨mem, rg3, pos⟩ .normal ⟨mem, rg3, pos⟩ 3 :=
      runs_store_iff.mpr ⟨workHeap, 0, by simp [Expr.eval, rg3, rg2, rg1, s0, startState],
        by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, by simp [hUpd0], rfl⟩
    have r5 : Runs w p ω
        (.call 7 outer [.reg 5, .reg 6, .reg 1, .reg 2, .const 0, .reg 3, .bin .add (.reg 3) (.const 1)])
        ⟨mem, rg3, pos⟩ .normal ⟨st1.mem, rg4, st1.pos⟩ (cOut + 10) := by
      refine runs_call_iff.mpr ⟨[treeHeap0, L, pathsBase, K, 0, workHeap, workHeap + 1], _, .returned w1, st1, cOut,
        ?_, hpOuter, hRunOut, rfl, rfl, ?_⟩
      · simp [evalArgs, Expr.eval, BinOp.eval, rg3, rg2, rg1, s0, startState,
          show 0 < 2 ^ w by omega, show 1 < 2 ^ w by omega, show workHeap + 1 < 2 ^ w by omega]
      · simp [argsSize, Expr.size]; omega
    have r6 : Runs w p ω (.assign 8 (.load (.reg 3))) ⟨st1.mem, rg4, st1.pos⟩ .normal ⟨st1.mem, rg5, st1.pos⟩ 3 :=
      runs_assign_iff.mpr ⟨st1.mem workHeap, by simp [Expr.eval, rg4, rg3, rg2, rg1, s0, startState], rfl, rfl, rfl⟩
    have rPre :=
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, r5, r6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    refine ⟨w1, _, cOut, st1, rg5, tok1, paths1, route1, steps1, rPre, by omega,
      by simp [rg5, rg4, rg3, rg2, rg1, s0, startState],
      by simp [rg5, rg4, rg3, rg2, rg1, s0, startState],
      by simp [rg5, rg4, rg3, rg2, rg1, s0, startState],
      by simp [rg5, rg4], by simp [rg5], hw1Lo, by simp only [Nat.sub_zero] at hw1Hi; omega,
      hS1, hSt1Bd, hmeta1, hfr1, hft1, ?_, ?_, by simp only [Nat.sub_zero] at hcOut; exact hcOut⟩
    · intro hFl0
      obtain ⟨_, hp10, _, _, hScan1⟩ := hZero1 hFl0
      refine ⟨fun e => by have h := (hHist1.2 steps1 le_rfl).2.2 e; rw [hS1.hRt, hS1.hR0] at h; exact h, ?_⟩
      apply pathCancel_no_reverse_of_scan hFforest ℓint hℓpos paths1 (fun q hq => (hS1.hPtOk q hq).2.2)
      intro p hp q hq _
      obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hp
      obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem hq
      rcases lt_trichotomy i' j' with hlt | rfl | hgt
      · simpa [hp10] using hScan1 i' j' (Nat.zero_le _) hlt (by rw [← hp10]; exact hj')
      · exact le_rfl
      · simpa [hp10, add_comm] using hScan1 j' i' (Nat.zero_le _) hgt (by rw [← hp10]; exact hi')
    · intro hFlNz
      rcases hNz1 hFlNz with h0 | hlt
      · exact absurd (hz workHeap le_rfl) h0
      · exact hlt
  induction rem with
  | zero =>
    intro workHeap pos steps mem tok paths route hremBd
      hrep hMatch hnum hoff hBd hPtAt hlen hPtOk hSame hHist hR0 hRt
      hlev hcap hhdl htreeH hnfPt hlocDisj htag18 hbelow hz hPtLt hDescLtPt hroom
    obtain ⟨w1, cPre, cOut, st1, rg5, tok1, paths1, route1, steps1, rPre, hcPre,
        _, _, _, hr5_7, hr5_8, hw1Lo, hw1Hi, hS1, hSt1Bd, hmeta1, hfr1, hft1, hDone1, hNz1, hcOut⟩ :=
      hPass hrep hMatch hnum hoff hBd hPtAt hlen hPtOk hSame hHist hR0 hRt
        hlev hcap hhdl htreeH hnfPt hlocDisj htag18 hbelow hz hPtLt hDescLtPt (by simpa using hroom)
    have hFl0 : st1.mem workHeap = 0 := by
      by_contra hnz; have := hNz1 hnz; omega
    obtain ⟨hFlowEq, hNoRev⟩ := hDone1 hFl0
    have r7 : Runs w p ω
        (.cond (.reg 8) (.call 9 self [.reg 0, .reg 1, .reg 2, .reg 7] ;; .ret (.reg 9)) (.ret (.reg 7)))
        ⟨st1.mem, rg5, st1.pos⟩ (.returned w1) ⟨st1.mem, rg5, st1.pos⟩ 4 :=
      runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, hr5_8, hFl0],
        by simp [runs_ret_iff, Expr.eval, hr5_7], by simp [Expr.size]⟩
    have rFull : Runs w p ω (cancelRoutePathsBody self outer)
        (startState [root, pathsBase, K, workHeap] mem pos) (.returned w1) ⟨st1.mem, rg5, st1.pos⟩ (cPre + 4 + 1) := by
      unfold cancelRoutePathsBody
      have h := runs_appendStmt rPre r7
      dsimp only [appendStmt] at h; exact h
    refine ⟨w1, _, ⟨st1.mem, rg5, st1.pos⟩, tok1, paths1, rFull,
      by omega, by simpa using hw1Hi, hS1.hlev, hS1.hcap, hS1.hrep, hmeta1, hS1.hMatch, hS1.hnum, hS1.hoff,
      hS1.hBd, hS1.hPtAt, hS1.hlen, hS1.hPtOk, hFlowEq, hNoRev,
      hS1.htag18, hS1.hz, hfr1, hft1, ?_⟩
    simp only [zero_add, one_mul]; dsimp only [Rrep] at hcOut ⊢; omega
  | succ rem ih =>
    intro workHeap pos steps mem tok paths route hremBd
      hrep hMatch hnum hoff hBd hPtAt hlen hPtOk hSame hHist hR0 hRt
      hlev hcap hhdl htreeH hnfPt hlocDisj htag18 hbelow hz hPtLt hDescLtPt hroom
    set S1 := K * K * (4 * pathApplySpace L + 2 * L) + 1
    have hSplitS1 : (rem + 1 + 1) * S1 = S1 + (rem + 1) * S1 := by ring
    obtain ⟨w1, cPre, cOut, st1, rg5, tok1, paths1, route1, steps1, rPre, hcPre,
        hr5_0, hr5_1, hr5_2, hr5_7, hr5_8, hw1Lo, hw1Hi, hS1, hSt1Bd, hmeta1, hfr1, hft1, hDone1, hNz1, hcOut⟩ :=
      hPass hrep hMatch hnum hoff hBd hPtAt hlen hPtOk hSame hHist hR0 hRt
        hlev hcap hhdl htreeH hnfPt hlocDisj htag18 hbelow hz hPtLt hDescLtPt (by omega)
    by_cases hFl0 : st1.mem workHeap = 0
    · obtain ⟨hFlowEq, hNoRev⟩ := hDone1 hFl0
      have r7 : Runs w p ω
          (.cond (.reg 8) (.call 9 self [.reg 0, .reg 1, .reg 2, .reg 7] ;; .ret (.reg 9)) (.ret (.reg 7)))
          ⟨st1.mem, rg5, st1.pos⟩ (.returned w1) ⟨st1.mem, rg5, st1.pos⟩ 4 :=
        runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, hr5_8, hFl0],
          by simp [runs_ret_iff, Expr.eval, hr5_7], by simp [Expr.size]⟩
      have rFull : Runs w p ω (cancelRoutePathsBody self outer)
          (startState [root, pathsBase, K, workHeap] mem pos) (.returned w1) ⟨st1.mem, rg5, st1.pos⟩ (cPre + 4 + 1) := by
        unfold cancelRoutePathsBody
        have h := runs_appendStmt rPre r7
        dsimp only [appendStmt] at h; exact h
      refine ⟨w1, _, ⟨st1.mem, rg5, st1.pos⟩, tok1, paths1, rFull,
        by omega, by omega, hS1.hlev, hS1.hcap, hS1.hrep, hmeta1, hS1.hMatch, hS1.hnum, hS1.hoff,
        hS1.hBd, hS1.hPtAt, hS1.hlen, hS1.hPtOk, hFlowEq, hNoRev,
        hS1.htag18, hS1.hz, hfr1, hft1, ?_⟩
      set C1 := K * K * (4 * pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 117 * L + 440) + 120
      have hMul : (rem + 1 + 1) * C1 = C1 + (rem + 1) * C1 := by ring
      dsimp only [Rrep] at hcOut ⊢; omega
    · have hLtSteps : steps < steps1 := hNz1 hFl0
      have hrem1 : 4 * K ^ 4 - steps1 ≤ rem := by omega
      obtain ⟨w2, cRec, st2, tok2, paths2, hRunRec, hw2Lo, hw2Hi,
          hlev2, hcap2, hrep2, hmeta2, hMatch2, hnum2, hoff2, hBd2, hPtAt2, hlen2,
          hConn2, hFlow2, hNoRev2, htag18_2, hz2, hfr2, hft2, hcRec⟩ :=
        ih hrem1 hS1.hrep hS1.hMatch hS1.hnum hS1.hoff hS1.hBd hS1.hPtAt hS1.hlen
          hS1.hPtOk hS1.hSameComp hS1.hHist hS1.hR0 hS1.hRt hS1.hlev hS1.hcap hS1.hhdl hS1.htreeH
          hS1.hnfPt hS1.hlocDisj hS1.htag18 hS1.hbelow hS1.hz (by omega) hS1.hDescLtPt (by omega)
      let rg6 := Function.update rg5 9 w2
      have hrCallRec : Runs w p ω (.call 9 self [.reg 0, .reg 1, .reg 2, .reg 7])
          ⟨st1.mem, rg5, st1.pos⟩ .normal ⟨st2.mem, rg6, st2.pos⟩ (cRec + 5) := by
        refine runs_call_iff.mpr ⟨[root, pathsBase, K, w1], _, .returned w2, st2, cRec,
          ?_, hpSelf, hRunRec, rfl, rfl, ?_⟩
        · simp [evalArgs, Expr.eval, hr5_0, hr5_1, hr5_2, hr5_7]
        · simp [argsSize, Expr.size]; omega
      have hrRet2 : Runs w p ω (.ret (.reg 9)) ⟨st2.mem, rg6, st2.pos⟩ (.returned w2) ⟨st2.mem, rg6, st2.pos⟩ 2 :=
        runs_ret_iff.mpr ⟨w2, by simp [Expr.eval, rg6], rfl, rfl, rfl⟩
      have r7 : Runs w p ω
          (.cond (.reg 8) (.call 9 self [.reg 0, .reg 1, .reg 2, .reg 7] ;; .ret (.reg 9)) (.ret (.reg 7)))
          ⟨st1.mem, rg5, st1.pos⟩ (.returned w2) ⟨st2.mem, rg6, st2.pos⟩ (1 + 1 + (cRec + 5 + 2 + 1)) := by
        refine runs_cond_iff.mpr ⟨st1.mem workHeap, cRec + 5 + 2 + 1, by simp [Expr.eval, hr5_8], ?_, by simp [Expr.size]; omega⟩
        rw [ite_eq_right hFl0]
        exact runs_seq_iff.mpr (Or.inr ⟨⟨st2.mem, rg6, st2.pos⟩, cRec + 5, 2, hrCallRec, hrRet2, rfl⟩)
      have rFull : Runs w p ω (cancelRoutePathsBody self outer)
          (startState [root, pathsBase, K, workHeap] mem pos) (.returned w2) ⟨st2.mem, rg6, st2.pos⟩
          (cPre + (1 + 1 + (cRec + 5 + 2 + 1)) + 1) := by
        unfold cancelRoutePathsBody
        have h := runs_appendStmt rPre r7
        dsimp only [appendStmt] at h; exact h
      have hfr02 : ∀ x < workHeap, (x < pathsBase ∨ pathsBase + 2 * K ≤ x) →
          ¬ Rrep.foot root tok x → st2.mem x = mem x := fun x hx hOut hnf =>
        (hfr2 x (by omega) hOut (fun hf => hnf (hft1 x hf))).trans (hfr1 x hx hOut hnf)
      have hft02 : ∀ x, Rrep.foot root tok2 x → Rrep.foot root tok x := fun x hf => hft1 x (hft2 x hf)
      refine ⟨w2, _, ⟨st2.mem, rg6, st2.pos⟩, tok2, paths2, rFull,
        by omega, by omega, hlev2, hcap2, hrep2, hmeta1.trans hmeta2, hMatch2, hnum2, hoff2, hBd2, hPtAt2, hlen2,
        hConn2, hFlow2, hNoRev2, htag18_2, hz2, hfr02, hft02, ?_⟩
      set C1 := K * K * (4 * pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 117 * L + 440) + 120
      have hMul : (rem + 1 + 1) * C1 = C1 + (rem + 1) * C1 := by ring
      dsimp only [Rrep] at hcOut hcRec ⊢; omega

/-- Top-level verification of `cancelRoutePathsBody` starting from `steps = 0`: runs in at most
`cancelRoutePathsSpace K L (pathApplySpace L)` scratch words and `cancelRoutePathsCost K L treeBudget`
amortized steps, preserving `solverStateRep`, `SelectHeapMatchesChain`, and `PathTreeNumericInv`
with zero footprint growth, and outputting a cancellation-free route with identical tree flow. -/
theorem cancelRoutePaths_runs
    {w L P m V psi k epsExp drainUnit initTree cmpExch self outer inner
      root descBase pathsBase K workHeap pos size maxEdges maxPaths : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {opTree : ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {loc : SelectHeapLoc}
    {ω : ℕ → Bool} {mem : ℕ → ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {B R : ℤ} {pathsInit : List (ℕ × ℕ)}
    (hw16 : 16 < 2 ^ w)
    (hfmt4 : fmt.limbBits = 4)
    (hlocalCore : Rcore.Local)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hCmpExch : ∀ ab cd ad cb : ℤ,
      MeetsContract w p cmpExch (pathCompareExchangeContract w 4 ab cd ad cb))
    (hpSelf : p.procs[self]? = some (cancelRoutePathsBody self outer))
    (hpOuter : p.procs[outer]? = some (cancelPairOuterBody outer inner))
    (hpInner : p.procs[inner]? = some (cancelPairInnerBody inner (opTree 3) cmpExch))
    (hFforest : model.chain.toTreeChain.chainTree.IsForest)
    (hFsub : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E)
    (hℓpos : ∀ e ∈ model.chain.toTreeChain.chainTree.E, 0 < model.extℓ (model.intToExt e))
    (hlogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hmaxE1 : 1 ≤ maxEdges) (hmaxEP : 2 * maxEdges ≤ maxPaths)
    (hcapE : 2 * (((maxEdges + maxPaths * model.extG.n : ℕ) : ℤ) * B) < (Num.capacity 4 L : ℤ))
    (hcapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hlocEnd : loc.endAddr ≤ descBase)
    (h2nW : 2 * model.extG.n + 1 < 2 ^ w)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hMatch : SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hoff : OffTreeRecInv model L mem tok.edgeRecords B)
    (hBd : OffTreeRecBound model L mem tok.edgeRecords B)
    (hPtAt : PathEndpointsAt mem pathsBase pathsInit)
    (hlen : pathsInit.length = K)
    (hPtOk : ∀ q ∈ pathsInit, q.1 < model.extG.n ∧ q.2 < model.extG.n ∧
      model.chain.toTreeChain.chainTree.Connected q.1 q.2)
    (hSame : ∀ p ∈ pathsInit, ∀ q ∈ pathsInit,
      model.chain.toTreeChain.chainTree.Connected p.1 q.1)
    (hnfPt : ∀ x < 2 * K, ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok (pathsBase + x))
    (hlocDisj : ∀ a, loc.hb ≤ a → a < loc.endAddr →
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a)
    (htag18 : ∀ a, tok.tag a = 18 → a < descBase)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < workHeap)
    (hz : ZeroFrom mem workHeap)
    (hPtLt : pathsBase + 2 * K ≤ workHeap)
    (hDescLtPt : descBase ≤ pathsBase)
    (hroom : workHeap + cancelRoutePathsSpace K L (pathApplySpace L) < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    let F := model.chain.toTreeChain.chainTree
    ∃ (work' cTot : ℕ) (st' : State) (tok' : SolverToken cfg L Rcore) (paths' : List (ℕ × ℕ)),
      Runs w p ω (cancelRoutePathsBody self outer)
        (startState [root, pathsBase, K, workHeap] mem pos) (.returned work') st' cTot ∧
      workHeap ≤ work' ∧
      work' ≤ workHeap + cancelRoutePathsSpace K L (pathApplySpace L) ∧
      tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
      Rrep.rep root model tok' st'.mem ∧ PreservesLevelMeta tok tok' mem st'.mem ∧
      SelectHeapMatchesChain st'.mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size ∧
      PathTreeNumericInv tok'.tree tok'.trees B R ∧
      OffTreeRecInv model L st'.mem tok'.edgeRecords B ∧
      OffTreeRecBound model L st'.mem tok'.edgeRecords B ∧
      PathEndpointsAt st'.mem pathsBase paths' ∧
      paths'.length = K ∧
      (∀ q ∈ paths', q.1 < model.extG.n ∧ q.2 < model.extG.n ∧ F.Connected q.1 q.2) ∧
      (∀ e, (paths'.map fun q => walkFlow (F.forestPath q.1 q.2) e).sum =
        (pathsInit.map fun q => walkFlow (F.forestPath q.1 q.2) e).sum) ∧
      (∀ (x : ℕ × Bool) p q, p ∈ paths' → q ∈ paths' → x ∈ F.forestPath p.1 p.2 →
        (x.1, !x.2) ∉ F.forestPath q.1 q.2) ∧
      (∀ a, tok'.tag a = 18 → a < descBase) ∧
      ZeroFrom st'.mem work' ∧
      (∀ x < workHeap, (x < pathsBase ∨ pathsBase + 2 * K ≤ x) →
        ¬ Rrep.foot root tok x → st'.mem x = mem x) ∧
      (∀ x, Rrep.foot root tok' x → Rrep.foot root tok x) ∧
      cTot + Rrep.phi root tok' st'.mem ≤
        cancelRoutePathsCost K L (pathTreeBudget LinkCut.PathProg.pathC L model.extG.n) +
          Rrep.phi root tok mem := by
  dsimp only
  unfold cancelRoutePathsSpace at hroom ⊢
  unfold cancelRoutePathsCost
  exact cancelRoutePaths_runs_aux (loc := loc) (levelsEnd0 := tok.levelsEnd) (intCap0 := tok.intCap)
    (handle0 := tok.handle) (treeHeap0 := tok.treeHeap)
    hw16 hfmt4 hlocalCore hTreeImpl hCmpExch hpSelf hpOuter hpInner hFforest hFsub hℓpos
    hlen (fun q hq => (hPtOk q hq).2.2) hlogW hmaxE1 hmaxEP hcapE hcapT hlocEnd h2nW
    (4 * K ^ 4) (route := fun _ => pathsInit) (steps := 0) (by omega)
    hrep hMatch hnum hoff hBd hPtAt hlen hPtOk hSame (validSwapSeq_zero _ _ _) rfl rfl
    rfl rfl rfl rfl hnfPt hlocDisj htag18 hbelow hz hPtLt hDescLtPt hroom

end MinCostFlow.MinRatio
