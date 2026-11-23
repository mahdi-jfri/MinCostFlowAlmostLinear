module

public import MinCostFlow.MinRatio.MinRatioMachineAssemblyBase
public import MinCostFlow.MinRatio.OrdShiftStepKFBL
import WordRAM.Tactic

/-!
# End-to-end deterministic Word-RAM machine execution for `Update`, `Query`, and `Detect`

Builds on the bundled 183-procedure table `solverOpsProcs` in `MinRatioMachineAssemblyBase.lean`
to prove the end-to-end execution theorems for Definition 4.5 (`minRatioMachineContractWithV`
operations `0` = `Update`, `1` = `Query`, `2` = `Detect`) against `solverStateRep` (with
`drainUnit := detectOffTreeDrainUnit F.limbs`) and
`Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / 2^k)`:
- `solverOps_query_runs`
- `solverOps_detect_runs`
- `solverOps_update_runs_credit`
- `solverOps_update_runs`
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num Scaling.Machine

/-- End-to-end execution of `minRatioMachineContractWithV` op 1 (`Query`) through the bundled
`solverOpsProcs` dispatch at `solverOpsDispatch base 1`. -/
theorem solverOps_query_runs
    {w base chainRefreshProc findCycleProc shiftLevelProc m V psi k epsExp root e heap pos : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph} {κ α : ℝ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg F.limbs Rcore}
    {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ}
    (hw : 14 ≤ w) (hfmt4 : F.fmt.limbBits = 4)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc))
    (hrep : (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).rep root model tok mem)
    (hpre : (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G m V κ α rate alloc).pre
      1 model [root, e, heap] mem)
    (hextEq : model.extG = G)
    (hbelow : ∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).foot root tok a → a < heap)
    (hz : ZeroFrom mem heap)
    (htreeWord : 2 * tok.tree.n + 1 < 2 ^ w)
    (htreeWidth : Nat.log 2 (2 * tok.tree.n + 1) ≤ 4 * F.limbs)
    (hfits : pathTreeFits 4 F.limbs tok.tree)
    (hfitsExp : ∀ slot, pathTreeActive tok.tree slot →
      pathTreeFits 4 F.limbs (lctExpose pathPayload tok.tree slot))
    (hroom : heap + max (F.limbs + LinkCut.PathProg.pathAlloc F.limbs 4 tok.tree.n
        [tok.treeHeap, mem (tok.slots + model.extToInt e), heap + F.limbs])
        (2 + 5 * F.limbs) + F.limbs < 2 ^ w) :
    let L := F.limbs
    let R := solverStateRep cfg L F.fmt.precision m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
    ∃ body, p.procs[solverOpsDispatch base 1]? = some body ∧
      ∃ ret cost out tok',
        Runs w p ω body (startState [root, e, heap] mem pos) (.returned ret) out cost ∧
        (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G m V κ α rate alloc).post
          1 model [root, e, heap] mem model out.mem ∧
        R.rep root model tok' out.mem ∧
        PreservesLevelMeta tok tok' mem out.mem ∧
        tok'.intCap = tok.intCap ∧
        ZeroFrom out.mem ret ∧ heap ≤ ret ∧
        ret ≤ heap + max (L + LinkCut.PathProg.pathAlloc L 4 tok.tree.n
          [tok.treeHeap, mem (tok.slots + model.extToInt e), heap + L]) (2 + 5 * L) + L ∧
        (∀ a < heap, ¬ R.foot root tok a → out.mem a = mem a) ∧
        (∀ a, R.foot root tok' a → R.foot root tok a ∨ (heap ≤ a ∧ a < ret)) ∧
        cost + R.phi root tok' out.mem ≤
          pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 53 * L + 160 + R.phi root tok mem ∧
        (∀ B R : ℤ, PathTreeNumericInv tok.tree tok.trees B R →
          PathTreeNumericInv tok'.tree tok'.trees B R) ∧
        tok'.edgeRecords = tok.edgeRecords ∧
        (∀ j < tok.intCap, out.mem (tok.edgeRecords + j) = mem (tok.edgeRecords + j)) := by
  have hall := solverOpsProcs_meetsAll hw hp
  have hw10 : 10 < 2 ^ w := lt_of_lt_of_le (by decide : 10 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw)
  refine ⟨_, hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  exact solverQueryBody_runs hlocalCore hfmt4 hextEq
    (hall.2.2.2.1 F.fmt F.limbs hfmt4) (hall.2.2.2.2.1 F.fmt.precision)
    (hall.2.2.2.2.2.1 F.fmt.precision) hrep hpre hbelow hz hw10 htreeWord htreeWidth
    hfits hfitsExp hroom

/-- End-to-end execution of `minRatioMachineContractWithV` op 2 (`Detect`) through the bundled
`solverOpsProcs` dispatch at `solverOpsDispatch base 2`. -/
theorem solverOps_detect_runs
    {w base chainRefreshProc findCycleProc shiftLevelProc m V psi k epsExp root heap pos : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph} {κ α : ℝ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg F.limbs Rcore}
    {B R : ℤ} {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ}
    (hw : 14 ≤ w) (hfmt4 : F.fmt.limbBits = 4) (hLpos : 0 < F.limbs)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc))
    (hExtRange : ∀ e < m, e ∈ model.extG.E)
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hcapB : 2 * ((2 * tok.tree.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 F.limbs : ℤ))
    (hthrB : ∀ e ∈ model.extG.E, |detectorThreshold F.fmt.precision cfg.ε (model.extℓ e)| ≤ B)
    (hfitNegTh : ∀ e ∈ model.extG.E, Num.Fits 4 F.limbs (-detectorThreshold F.fmt.precision cfg.ε (model.extℓ e)))
    (hrep : (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).rep root model tok mem)
    (hpre : (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G m V κ α rate alloc).pre
      2 model [root, heap] mem)
    (hbelow : ∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).foot root tok a → a < heap)
    (hz : ZeroFrom mem heap)
    (htreeWord : 2 * tok.tree.n + 1 < 2 ^ w)
    (htreeWidth : Nat.log 2 (2 * tok.tree.n + 1) ≤ 4 * F.limbs)
    (hroom : heap + 1 + m + ((algorithm2_detect cfg model).1.card + 1) * detectTreeRoundSpace F.limbs +
      tok.offReadyCount * (2 + 4 * F.limbs) < 2 ^ w) :
    let L := F.limbs
    let Rrep := solverStateRep cfg L F.fmt.precision m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
    let S := (algorithm2_detect cfg model).1
    ∃ body, p.procs[solverOpsDispatch base 2]? = some body ∧
      ∃ ret cost out tok',
        Runs w p ω body (startState [root, heap] mem pos) (.returned ret) out cost ∧
        (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg κ) G m V κ α rate alloc).post
          2 model [root, heap] mem (algorithm2_detect cfg model).2 out.mem ∧
        Rrep.rep root (algorithm2_detect cfg model).2 tok' out.mem ∧
        PreservesLevelMeta tok tok' mem out.mem ∧
        tok'.intCap = tok.intCap ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        ZeroFrom out.mem ret ∧ heap ≤ ret ∧
        ret ≤ heap + 1 + m + (S.card + 1) * detectTreeRoundSpace L + tok.offReadyCount * (2 + 4 * L) ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < ret)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          (S.card + 1) * (detectTreeStepBudget L model.extG.n + 2) + 200 + Rrep.phi root tok mem ∧
        (OffTreeRecSep model L mem tok.edgeRecords →
          OffTreeRecSep (algorithm2_detect cfg model).2 L out.mem tok'.edgeRecords) := by
  have hall := solverOpsProcs_meetsAll hw hp
  have hw13 : 13 < 2 ^ w := lt_of_lt_of_le (by decide : 13 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw)
  refine ⟨_, hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, ?_⟩
  exact solverDetectBody_runs hlocalCore hfmt4 hExtRange
    (hall.2.2.2.1 F.fmt F.limbs hfmt4) hall.2.2.1 hall.2.2.2.2.2.2.1
    heps hlen hnum hcapB hthrB hfitNegTh hrep hpre hbelow hz hw13 hLpos htreeWord htreeWidth hroom

/-- Credit-bearing execution of `minRatioMachineContractWithV` op 0 (`Update`) through the bundled
`solverOpsProcs` dispatch at `solverOpsDispatch base 0`, threading
`toolMul * Δ totalRuntime + treeMul * Δ totalTreeUpdates`. -/
theorem solverOps_update_runs_credit
    {w base chainRefreshProc findCycleProc shiftLevelProc m U_cap V psi k epsExp capExp limbMul
      capLimit findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths toolMul treeMul
      root batch g l eta heap pos : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg F.limbs Rcore}
    {B_bound R_bound : ℤ}
    {refreshSpace refreshBudget : ℕ → ℕ} {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ}
    (hMono : toolMul = 0 ∨ ToolCostMono cfg.T)
    (hw : 14 ≤ w) (hfmt4 : F.fmt.limbBits = 4) (hV : cfg.ValidOrdNoHidden)
    (hPL : F.fmt.precision ≤ 4 * F.limbs)
    (hα : cfg.α = Num.IPM.alphaPrime m U_cap / 8)
    (hepsExp : epsExp = k + Num.IPM.alphaExponent m U_cap + 10)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc))
    (hRefresh : ChainRefreshStepSpecW w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p chainRefreshProc refreshSpace
      refreshBudget toolMul treeMul B_bound R_bound)
    (hFind : FindCycleStepSpecW w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p findCycleProc findSpace findBudget
      maxEdges maxPaths)
    (hShift : ShiftLevelStepSpecW w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p shiftLevelProc shiftSpace
      shiftBudget toolMul treeMul)
    (hBridge : GoodCycleNumericBridge F cfg G m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore maxEdges maxPaths B_bound R_bound)
    (hrep : (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).rep root model tok mem)
    (hCapFacts : WireCapFacts capExp limbMul F.limbs capLimit model)
    (hpre : (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
      G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc).pre 0 model [root, batch, g, l, eta, heap] mem)
    (hextEq : model.extG = G)
    (hBr : BranchesLtK cfg model)
    (hbelow : ∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).foot root tok a → a < heap)
    (hGE : ∀ e < m, e ∈ G.E)
    (hz : ZeroFrom mem heap)
    (hmPos : 0 < m) (hcapPos : 0 < tok.intCap)
    (hnfLe : model.nextFresh ≤ tok.intCap)
    (h5L1W : 5 * F.limbs + 1 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) (hepsW : epsExp < 2 ^ w)
    (hpsiLimW : ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ < 2 ^ w)
    (h2nW : 2 * G.n + 1 < 2 ^ w) (hlogW : Nat.log 2 (2 * G.n + 1) ≤ 4 * F.limbs)
    (hsizeM : Nat.size m ≤ F.rangeExponent + 8)
    (hmaxEP : maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20))
    (hcapEvalB : 2 * (((maxEdges + maxPaths * G.n : ℕ) : ℤ) * B_bound) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapTreeB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) *
      ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
        (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapOffB : B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
      (Num.capacity 4 F.limbs : ℤ))
    (hroom : ∀ U, BatchAt mem batch U →
      let model1 := alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m) (readVector mem l 4 F.limbs F.fmt.precision m)
      heap + updateSpaceBound F.limbs m cfg.P.d model.nextFresh U.length (loopStepBound cfg model1)
        findSpace shiftSpace
        maxEdges maxPaths (refreshSpace U.length) + 2 < 2 ^ w)
    (hquotasW : ∀ U, BatchAt mem batch U →
      let model1 := alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m) (readVector mem l 4 F.limbs F.fmt.precision m)
      ∀ i ≤ cfg.P.d,
        shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i < 2 ^ w)
    (hLoopInv : ∀ U, BatchAt mem batch U →
      Chain.Ordered.ShiftLoopChainInv cfg (alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m)
        (readVector mem l 4 F.limbs F.fmt.precision m)).chain) :
    let L := F.limbs
    let P := F.fmt.precision
    let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
    ∃ body, p.procs[solverOpsDispatch base 0]? = some body ∧
      ∃ ret cost out model' tok',
        Runs w p ω body (startState [root, batch, g, l, eta, heap] mem pos) (.returned ret) out cost ∧
        (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
          G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc).post 0 model [root, batch, g, l, eta, heap] mem model' out.mem ∧
        Rrep.rep root model' tok' out.mem ∧
        (∀ U, BatchAt mem batch U →
          tok'.intCap =
            (if tok.intCap < model.nextFresh + U.length then 2 * (model.nextFresh + U.length) else tok.intCap)) ∧
        ZeroFrom out.mem ret ∧ heap ≤ ret ∧
        (∀ U, BatchAt mem batch U →
          let model1 := alg2PreLoopState cfg model U (readVector mem g 4 L P m) (readVector mem l 4 L P m)
          let N := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain
          ret ≤ heap + updateSpaceBound L m cfg.P.d model.nextFresh U.length (loopStepBound cfg model1)
            findSpace shiftSpace maxEdges maxPaths (refreshSpace U.length) ∧
          cost + Rrep.phi root tok' out.mem +
              shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model'.chain *
                cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
              toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
            updateBudgetBound L cfg.P.d G.n tok.intCap model.nextFresh U.length N findBudget shiftBudget
              maxEdges maxPaths (detectOffTreeDrainUnit L) (refreshBudget U.length) +
            Rrep.phi root tok mem +
            toolMul * model'.chain.totalRuntime + treeMul * model'.chain.totalTreeUpdates) ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < ret)) ∧
        ∃ B R : ℤ, PathTreeNumericInv tok'.tree tok'.trees B R ∧
          B ≤ B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) ∧
          R ≤ R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) := by
  have hall := solverOpsProcs_meetsAll hw hp
  have hw16 : 16 < 2 ^ w := lt_of_lt_of_le (by decide : 16 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw)
  obtain ⟨bR, hbR, hR⟩ := hRefresh
  obtain ⟨bS, hbS, hS⟩ := hShift
  refine ⟨_, hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  obtain ⟨ret, cost, out, model', tok', hr, hpost, hrep', _, hcap', hz', hlo, hrc, hfr, hft, hnum⟩ :=
    solverUpdateBody_runs_credit_gen hlocalCore (fun _ _ _ => True)
      (fun _ _ _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
      hMono hV hfmt4 hPL hα hepsExp
      hall.2.2.2.2.2.2.2.2.2.2.2.2.1 hall.1 hall.2.2.2.2.2.2.2.1
      ⟨bR, hbR, fun r u g l qB h pos ω m0 mem stM t U _ h1 _ h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
          h13 h14 h15 h16 h17 h18 h19 _ _ => by
        obtain ⟨nh, c, o, t', B', R', hr, hlo, hhi, hlv, hic, hB, hR', hrep', hn', ho', hb', hq',
            hp', hz', hfr', hft', hc'⟩ :=
          hR r u g l qB h pos ω m0 mem stM t U h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
            h16 h17 h18 h19
        exact ⟨nh, c, o, t', B', R', hr, hlo, hhi, hlv, hic, hB, hR', hrep', trivial, hn', ho',
          hb', hq', hp', hz', hfr', hft', hc'⟩⟩
      hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hFind
      (hall.2.2.2.2.2.2.2.2.1 m U_cap k F.fmt.precision) hall.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      ⟨bS, hbS, fun r h pos i ω mem stM t B R h1 h2 h3 h4 h5 h6 _ h7 h8 h9 h10 h11 h12 h13 h14
          h15 h16 => by
        obtain ⟨nh, c, o, t', hr, hlo, hhi, hlv, hic, hrep', hn', ho', hb', hz', hfr', hft', hc'⟩ :=
          hS r h pos i ω mem stM t B R h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
        exact ⟨nh, c, o, t', hr, hlo, hhi, hlv, hic, hrep', trivial, hn', ho', hb', hz', hfr',
          hft', hc'⟩⟩
      hall.2.1 hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hall.2.2.2.2.2.2.2.2.2.1
      hall.2.2.2.2.2.2.2.2.2.2.1 (hall.2.2.2.1 F.fmt F.limbs hfmt4)
      (hall.2.2.2.2.2.2.2.2.2.2.2.1 F.limbs) hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hall.2.2.1
      hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hBridge hrep trivial hCapFacts hpre hextEq hBr
      hbelow hGE hz hmPos hcapPos hnfLe hw16 h5L1W F.parameters_fit.2.1 hdW hepsW hpsiLimW
      h2nW hlogW hsizeM hmaxEP hcapEvalB hcapTreeB hcapOffB hroom hquotasW hLoopInv
  exact ⟨ret, cost, out, model', tok', hr, hpost, hrep', hcap', hz', hlo, hrc, hfr, hft, hnum⟩

/-- Credit-bearing execution of `minRatioMachineContractWithV` op 0 (`Update`) under the `KFBL`
layout contract: takes `ChainRefreshStepSpecWKFBL` and `ShiftLevelStepSpecWKFBL`, and maintains
`SolverLevelCapsInv P V vCap eCap` and `DeepInv`. -/
theorem solverOps_update_runs_credit_kfbl
    {w base chainRefreshProc findCycleProc shiftLevelProc m U_cap V psi k epsExp capExp limbMul
      capLimit wordExp stretchPrec intCapMax forestEdgeCap vCap eCap findSpace findBudget
      shiftSpace shiftBudget maxEdges maxPaths toolMul treeMul root batch g l eta heap pos : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg F.limbs Rcore}
    {B_bound R_bound : ℤ}
    {refreshSpace refreshBudget : ℕ → ℕ} {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ}
    {DeepInv : ChainState cfg.T cfg.P → Prop}
    (hMono : toolMul = 0 ∨ ToolCostMono cfg.T)
    (hw : 14 ≤ w) (hfmt4 : F.fmt.limbBits = 4) (hV : cfg.ValidOrdNoHidden)
    (hPL : F.fmt.precision ≤ 4 * F.limbs)
    (hα : cfg.α = Num.IPM.alphaPrime m U_cap / 8)
    (hepsExp : epsExp = k + Num.IPM.alphaExponent m U_cap + 10)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc))
    (hRefresh : ChainRefreshStepSpecWKFBL w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit vCap eCap cfg Rcore p
      chainRefreshProc refreshSpace refreshBudget toolMul treeMul B_bound R_bound)
    (hFind : FindCycleStepSpecW w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p findCycleProc findSpace findBudget
      maxEdges maxPaths)
    (hShift : ShiftLevelStepSpecWKFBL w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap cfg Rcore p shiftLevelProc shiftSpace shiftBudget toolMul treeMul)
    (hBridge : GoodCycleNumericBridge F cfg G m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore maxEdges maxPaths B_bound R_bound)
    (hFEdgeCap : 2 * G.n ≤ forestEdgeCap)
    (hDeepPreLoop : ∀ U gVec lVec, RefreshBatch G U →
      (∀ e ∈ G.E, (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ lVec e ∧ lVec e ≤ (2 : ℝ) ^ F.rangeExponent) →
      (∀ e ∈ G.E, ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ F.fmt.precision = lVec e) →
      (∀ e ∈ G.E, (∀ u ∈ U, ¬ u.Inserts e) → gVec e = model.extg e ∧ lVec e = model.extℓ e) →
      DeepInv model.chain → DeepInv (alg2PreLoopState cfg model U gVec lVec).chain)
    (hDeepShift : ∀ ch, Chain.Ordered.ShiftLoopChainInv cfg ch → DeepInv ch →
      ∀ i ≤ cfg.P.d, DeepInv (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P ch i).1)
    (hDeepToModel : ∀ (stM : Alg2State cfg) (i : Fin (cfg.P.d + 1)), i.val < cfg.P.d →
      Chain.Ordered.ShiftLoopChainInv cfg stM.chain → DeepInv stM.chain →
      ShiftDeepModelInv w F.limbs F.fmt.precision wordExp stretchPrec stM i)
    (hrep : (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).rep root model tok mem)
    (hCaps : SolverLevelCapsInv F.fmt.precision V vCap eCap model tok mem)
    (hDeep : DeepInv model.chain)
    (hIntCap : tok.intCap ≤ intCapMax)
    (hNoGrow : ∀ U, BatchAt mem batch U → model.nextFresh + U.length ≤ tok.intCap)
    (hCapFacts : WireCapFacts capExp limbMul F.limbs capLimit model)
    (hpre : (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
      G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc).pre 0 model [root, batch, g, l, eta, heap] mem)
    (hextEq : model.extG = G)
    (hBr : BranchesLtK cfg model)
    (hbelow : ∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).foot root tok a → a < heap)
    (hGE : ∀ e < m, e ∈ G.E)
    (hz : ZeroFrom mem heap)
    (hmPos : 0 < m) (hcapPos : 0 < tok.intCap)
    (hnfLe : model.nextFresh ≤ tok.intCap)
    (h5L1W : 5 * F.limbs + 1 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) (hepsW : epsExp < 2 ^ w)
    (hpsiLimW : ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ < 2 ^ w)
    (h2nW : 2 * G.n + 1 < 2 ^ w) (hlogW : Nat.log 2 (2 * G.n + 1) ≤ 4 * F.limbs)
    (hsizeM : Nat.size m ≤ F.rangeExponent + 8)
    (hmaxEP : maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20))
    (hcapEvalB : 2 * (((maxEdges + maxPaths * G.n : ℕ) : ℤ) * B_bound) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapTreeB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) *
      ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
        (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapOffB : B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
      (Num.capacity 4 F.limbs : ℤ))
    (hroom : ∀ U, BatchAt mem batch U →
      let model1 := alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m) (readVector mem l 4 F.limbs F.fmt.precision m)
      heap + updateSpaceBound F.limbs m cfg.P.d model.nextFresh U.length (loopStepBound cfg model1)
        findSpace shiftSpace
        maxEdges maxPaths (refreshSpace U.length) + 2 < 2 ^ w)
    (hquotasW : ∀ U, BatchAt mem batch U →
      let model1 := alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m) (readVector mem l 4 F.limbs F.fmt.precision m)
      ∀ i ≤ cfg.P.d,
        shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i < 2 ^ w)
    (hLoopInv : ∀ U, BatchAt mem batch U →
      Chain.Ordered.ShiftLoopChainInv cfg (alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m)
        (readVector mem l 4 F.limbs F.fmt.precision m)).chain) :
    let L := F.limbs
    let P := F.fmt.precision
    let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
    ∃ body, p.procs[solverOpsDispatch base 0]? = some body ∧
      ∃ ret cost out model' tok',
        Runs w p ω body (startState [root, batch, g, l, eta, heap] mem pos) (.returned ret) out cost ∧
        (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
          G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc).post 0 model [root, batch, g, l, eta, heap] mem model' out.mem ∧
        Rrep.rep root model' tok' out.mem ∧
        SolverLevelCapsInv P V vCap eCap model' tok' out.mem ∧
        DeepInv model'.chain ∧
        (∀ U, BatchAt mem batch U →
          tok'.intCap =
            (if tok.intCap < model.nextFresh + U.length then 2 * (model.nextFresh + U.length) else tok.intCap)) ∧
        ZeroFrom out.mem ret ∧ heap ≤ ret ∧
        (∀ U, BatchAt mem batch U →
          let model1 := alg2PreLoopState cfg model U (readVector mem g 4 L P m) (readVector mem l 4 L P m)
          let N := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain
          ret ≤ heap + updateSpaceBound L m cfg.P.d model.nextFresh U.length (loopStepBound cfg model1)
            findSpace shiftSpace maxEdges maxPaths (refreshSpace U.length) ∧
          cost + Rrep.phi root tok' out.mem +
              shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model'.chain *
                cycleLoopIterBudget L cfg.P.d findBudget shiftBudget +
              toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates ≤
            updateBudgetBound L cfg.P.d G.n tok.intCap model.nextFresh U.length N findBudget shiftBudget
              maxEdges maxPaths (detectOffTreeDrainUnit L) (refreshBudget U.length) +
            Rrep.phi root tok mem +
            toolMul * model'.chain.totalRuntime + treeMul * model'.chain.totalTreeUpdates) ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < ret)) ∧
        ∃ B R : ℤ, PathTreeNumericInv tok'.tree tok'.trees B R ∧
          B ≤ B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) ∧
          R ≤ R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) := by
  have hall := solverOpsProcs_meetsAll hw hp
  have hw16 : 16 < 2 ^ w := lt_of_lt_of_le (by decide : 16 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw)
  obtain ⟨bR, hbR, hR⟩ := hRefresh
  obtain ⟨bS, hbS, hS⟩ := hShift
  let Inv : Alg2State cfg → SolverToken cfg F.limbs Rcore → (ℕ → ℕ) → Prop :=
    fun stM t mem' =>
      SolverLevelCapsInv F.fmt.precision V vCap eCap stM t mem' ∧ DeepInv stM.chain ∧
      t.intCap ≤ intCapMax ∧ (stM.chain.G 0).n ≤ G.n
  have hInvMeta : ∀ stM1 stM2 t t' m1 m2,
      (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) Rcore).rep root stM1 t m1 →
      Inv stM1 t m1 → PreservesLevelMeta t t' m1 m2 → stM2.chain = stM1.chain →
      (t'.intCap = t.intCap ∨
        (stM2 = model ∧ t = tok ∧ ∃ U, BatchAt mem batch U ∧
          t'.intCap = if t.intCap < model.nextFresh + U.length then 2 * (model.nextFresh + U.length) else t.intCap)) →
      Inv stM2 t' m2 := by
    intro stM1 stM2 t t' m1 m2 _ ⟨hC, hD, hI, hGn⟩ hPres hch hcapOr
    have hC' : SolverLevelCapsInv F.fmt.precision V vCap eCap stM2 t' m2 :=
      hPres.to_capsInv hC (by rw [hch]) (fun _ _ => by rw [hch]) (fun _ _ => by rw [hch])
        (fun _ _ => by rw [hch]) (fun _ _ => by rw [hch]) (by rw [hch])
    have hI' : t'.intCap ≤ intCapMax := by
      rcases hcapOr with heq | ⟨_, rfl, U, hBU, hite⟩
      · exact heq ▸ hI
      · have hng := hNoGrow U hBU
        rw [hite, ite_eq_right (by omega)]
        exact hI
    exact ⟨hC', hch ▸ hD, hI', hch ▸ hGn⟩
  have hInvMem : ∀ stM t m1 m2,
      (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) Rcore).rep root stM t m1 →
      Inv stM t m1 →
      (∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) Rcore).foot root t a → m2 a = m1 a) →
      Inv stM t m2 := by
    intro stM t m1 m2 hrep' ⟨hC, hD, hI, hGn⟩ hag
    have hPres : PreservesLevelMeta t t m1 m2 :=
      (PreservesLevelMeta.refl t m1).congr_mem_right fun a ht =>
        hag a (LevelMetaFoot.mem_foot hrep' ht)
    exact ⟨hPres.to_capsInv hC rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) rfl, hD, hI, hGn⟩
  refine ⟨_, hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  obtain ⟨ret, cost, out, model', tok', hr, hpost, hrep', ⟨hCaps', hDeep', _, _⟩, hcap', hz', hlo,
      hrc, hfr, hft, hnum⟩ :=
    solverUpdateBody_runs_credit_gen hlocalCore Inv hInvMeta hInvMem hMono hV hfmt4 hPL hα hepsExp
      hall.2.2.2.2.2.2.2.2.2.2.2.2.1 hall.1 hall.2.2.2.2.2.2.2.1
      ⟨bR, hbR, fun r u g' l' qB h pos ω m0 mem' stM t U hEqM h1 ⟨hC, hD, hI, _⟩ h2 h3 h4 h5 h6 h7 h8
          h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hLenIn hGridIn => by
        obtain ⟨nh, c, o, t', B', R', hr, hlo, hhi, hlv, hic, hB, hR', hrep', hM', hC', hn', ho',
            hb', hq', hp', hz', hfr', hft', hc'⟩ :=
          hR r u g' l' qB h pos ω m0 mem' stM t U h1 hC.1 hC.2 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
            h12 h13 h14 h15 h16 h17 h18 h19
        have hD' : DeepInv (alg2PreLoopState cfg stM U
            (updateOverlay stM.extG.E U (readVector m0 g' 4 F.limbs F.fmt.precision m) stM.extg)
            (updateOverlay stM.extG.E U (readVector m0 l' 4 F.limbs F.fmt.precision m) stM.extℓ)).chain := by
          subst hEqM
          refine hDeepPreLoop U _ _ (hextEq ▸ h8) (hextEq ▸ hLenIn) (hextEq ▸ hGridIn) ?_ hD
          intro e he hNo
          have hni : ¬ (∃ u ∈ U, u.Inserts e) := fun ⟨u, hu, hi⟩ => hNo u hu hi
          simp [updateOverlay, hextEq, he, hni]
        have hGn' : ((alg2PreLoopState cfg stM U
            (updateOverlay stM.extG.E U (readVector m0 g' 4 F.limbs F.fmt.precision m) stM.extg)
            (updateOverlay stM.extG.E U (readVector m0 l' 4 F.limbs F.fmt.precision m) stM.extℓ)).chain.G 0).n ≤ G.n := by
          have hstExt : stM.extG = G := hEqM ▸ hextEq
          have hExt1 : (alg2PreLoopState cfg stM U
              (updateOverlay stM.extG.E U (readVector m0 g' 4 F.limbs F.fmt.precision m) stM.extg)
              (updateOverlay stM.extG.E U (readVector m0 l' 4 F.limbs F.fmt.precision m) stM.extℓ)).extG = G := by
            dsimp only [alg2PreLoopState]
            rw [(translateBatch_preserves U stM.extG (stM.chain.G 0) stM.extToInt stM.intToExt
              stM.nextFresh h1.2.2.2.2.1 h8.1).1, h8.2.1, hstExt]
          rw [hrep'.2.2.2.2.1.n_eq, hExt1]
        exact ⟨nh, c, o, t', B', R', hr, hlo, hhi, hlv, hic, hB, hR', hrep',
          ⟨⟨hM', hC'⟩, hD', hic ▸ hI, hGn'⟩, hn', ho', hb', hq', hp', hz', hfr', hft', hc'⟩⟩
      hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hFind
      (hall.2.2.2.2.2.2.2.2.1 m U_cap k F.fmt.precision) hall.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      ⟨bS, hbS, fun r h pos i ω mem' stM t B R h1 h2 h3 h4 h5 h6 ⟨hC, hD, hI, hGn⟩ hLoop h7 h8 h9 h10
          h11 h12 h13 h14 h15 => by
        have hFEdge : 2 * (stM.chain.G 0).n ≤ forestEdgeCap := by omega
        obtain ⟨nh, c, o, t', hr, hlo, hhi, hlv, hic, _, _, _, _, hrep', hM', hC', hn', ho', hb',
            hz', hfr', hft', hc'⟩ :=
          hS r h pos i ω mem' stM t B R h1 h2 h3 h4 h5 h6 hC.1 hC.2 hLoop
            (fun hiD => hDeepToModel stM i hiD hLoop hD) hI hFEdge h7 h8 h9 h10 h11 h12 h13 h14 h15
        have hD' : DeepInv (alg2LoopShiftStep cfg stM i).chain :=
          hDeepShift stM.chain hLoop hD i.val (Nat.lt_succ_iff.mp i.isLt)
        have hGn' : ((alg2LoopShiftStep cfg stM i).chain.G 0).n ≤ G.n := by
          have heq1 : ((alg2LoopShiftStep cfg stM i).chain.G 0).n = (alg2LoopShiftStep cfg stM i).extG.n :=
            hrep'.2.2.2.2.1.n_eq
          have heq2 : (stM.chain.G 0).n = stM.extG.n := h6.2.2.2.2.1.n_eq
          have heq3 : (alg2LoopShiftStep cfg stM i).extG = stM.extG := rfl
          rw [heq1, heq3, ← heq2]
          exact hGn
        exact ⟨nh, c, o, t', hr, hlo, hhi, hlv, hic, hrep', ⟨⟨hM', hC'⟩, hD', hic ▸ hI, hGn'⟩, hn', ho',
          hb', hz', hfr', hft', hc'⟩⟩
      hall.2.1 hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hall.2.2.2.2.2.2.2.2.2.1
      hall.2.2.2.2.2.2.2.2.2.2.1 (hall.2.2.2.1 F.fmt F.limbs hfmt4)
      (hall.2.2.2.2.2.2.2.2.2.2.2.1 F.limbs) hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hall.2.2.1
      hall.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hBridge hrep
      ⟨hCaps, hDeep, hIntCap, by rw [hrep.2.2.2.2.1.n_eq, hextEq]⟩ hCapFacts
      hpre hextEq hBr hbelow hGE hz hmPos hcapPos hnfLe hw16 h5L1W F.parameters_fit.2.1 hdW hepsW
      hpsiLimW h2nW hlogW hsizeM hmaxEP hcapEvalB hcapTreeB hcapOffB hroom hquotasW hLoopInv
  exact ⟨ret, cost, out, model', tok', hr, hpost, hrep', hCaps', hDeep', hcap', hz', hlo, hrc,
      hfr, hft, hnum⟩

/-- End-to-end execution of `minRatioMachineContractWithV` op 0 (`Update`) through the bundled
`solverOpsProcs` dispatch at `solverOpsDispatch base 0`. The cost clause charges the shift loop
by its actual number of iterations: the unused shift quota `shiftRemainingBudget` of the final
chain, times `cycleLoopIterBudget`, stands on the left side, so the quota that the loop uses is
paid out of the quota `N` of the chain before the loop. -/
theorem solverOps_update_runs
    {w base chainRefreshProc findCycleProc shiftLevelProc m U_cap V psi k epsExp capExp limbMul
      capLimit findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths
      root batch g l eta heap pos : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg F.limbs Rcore}
    {B_bound R_bound : ℤ}
    {refreshSpace refreshBudget : ℕ → ℕ} {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ}
    (hw : 14 ≤ w) (hfmt4 : F.fmt.limbBits = 4) (hV : cfg.ValidOrdNoHidden)
    (hPL : F.fmt.precision ≤ 4 * F.limbs)
    (hα : cfg.α = Num.IPM.alphaPrime m U_cap / 8)
    (hepsExp : epsExp = k + Num.IPM.alphaExponent m U_cap + 10)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc))
    (hRefresh : ChainRefreshStepSpecW w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p chainRefreshProc refreshSpace
      refreshBudget 0 0 B_bound R_bound)
    (hFind : FindCycleStepSpecW w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p findCycleProc findSpace findBudget
      maxEdges maxPaths)
    (hShift : ShiftLevelStepSpecW w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p shiftLevelProc shiftSpace
      shiftBudget 0 0)
    (hBridge : GoodCycleNumericBridge F cfg G m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore maxEdges maxPaths B_bound R_bound)
    (hrep : (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).rep root model tok mem)
    (hCapFacts : WireCapFacts capExp limbMul F.limbs capLimit model)
    (hpre : (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
      G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc).pre 0 model [root, batch, g, l, eta, heap] mem)
    (hextEq : model.extG = G)
    (hBr : BranchesLtK cfg model)
    (hbelow : ∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).foot root tok a → a < heap)
    (hGE : ∀ e < m, e ∈ G.E)
    (hz : ZeroFrom mem heap)
    (hmPos : 0 < m) (hcapPos : 0 < tok.intCap)
    (hnfLe : model.nextFresh ≤ tok.intCap)
    (h5L1W : 5 * F.limbs + 1 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) (hepsW : epsExp < 2 ^ w)
    (hpsiLimW : ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ < 2 ^ w)
    (h2nW : 2 * G.n + 1 < 2 ^ w) (hlogW : Nat.log 2 (2 * G.n + 1) ≤ 4 * F.limbs)
    (hsizeM : Nat.size m ≤ F.rangeExponent + 8)
    (hmaxEP : maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20))
    (hcapEvalB : 2 * (((maxEdges + maxPaths * G.n : ℕ) : ℤ) * B_bound) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapTreeB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) *
      ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
        (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
      (Num.capacity 4 F.limbs : ℤ))
    (hcapOffB : B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
      (Num.capacity 4 F.limbs : ℤ))
    (hroom : ∀ U, BatchAt mem batch U →
      let model1 := alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m) (readVector mem l 4 F.limbs F.fmt.precision m)
      heap + updateSpaceBound F.limbs m cfg.P.d model.nextFresh U.length (loopStepBound cfg model1)
        findSpace shiftSpace
        maxEdges maxPaths (refreshSpace U.length) + 2 < 2 ^ w)
    (hquotasW : ∀ U, BatchAt mem batch U →
      let model1 := alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m) (readVector mem l 4 F.limbs F.fmt.precision m)
      ∀ i ≤ cfg.P.d,
        shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i < 2 ^ w)
    (hLoopInv : ∀ U, BatchAt mem batch U →
      Chain.Ordered.ShiftLoopChainInv cfg (alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m)
        (readVector mem l 4 F.limbs F.fmt.precision m)).chain) :
    let L := F.limbs
    let P := F.fmt.precision
    let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
    ∃ body, p.procs[solverOpsDispatch base 0]? = some body ∧
      ∃ ret cost out model' tok',
        Runs w p ω body (startState [root, batch, g, l, eta, heap] mem pos) (.returned ret) out cost ∧
        (minRatioMachineContractWithV F (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
          G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc).post 0 model [root, batch, g, l, eta, heap] mem model' out.mem ∧
        Rrep.rep root model' tok' out.mem ∧
        (∀ U, BatchAt mem batch U →
          tok'.intCap =
            (if tok.intCap < model.nextFresh + U.length then 2 * (model.nextFresh + U.length) else tok.intCap)) ∧
        ZeroFrom out.mem ret ∧ heap ≤ ret ∧
        (∀ U, BatchAt mem batch U →
          let model1 := alg2PreLoopState cfg model U (readVector mem g 4 L P m) (readVector mem l 4 L P m)
          let N := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain
          ret ≤ heap + updateSpaceBound L m cfg.P.d model.nextFresh U.length (loopStepBound cfg model1)
            findSpace shiftSpace maxEdges maxPaths (refreshSpace U.length) ∧
          cost + Rrep.phi root tok' out.mem +
              shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model'.chain *
                cycleLoopIterBudget L cfg.P.d findBudget shiftBudget ≤
            updateBudgetBound L cfg.P.d G.n tok.intCap model.nextFresh U.length N findBudget shiftBudget
              maxEdges maxPaths (detectOffTreeDrainUnit L) (refreshBudget U.length) + Rrep.phi root tok mem) ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < ret)) ∧
        ∃ B R : ℤ, PathTreeNumericInv tok'.tree tok'.trees B R ∧
          B ≤ B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) ∧
          R ≤ R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) := by
  simpa using solverOps_update_runs_credit (toolMul := 0) (treeMul := 0) hlocalCore (Or.inl rfl)
    hw hfmt4 hV hPL hα hepsExp hp hRefresh hFind hShift hBridge hrep hCapFacts hpre hextEq hBr
    hbelow hGE hz hmPos hcapPos hnfLe h5L1W hdW hepsW hpsiLimW h2nW hlogW hsizeM hmaxEP
    hcapEvalB hcapTreeB hcapOffB hroom hquotasW hLoopInv

end MinCostFlow.MinRatio
