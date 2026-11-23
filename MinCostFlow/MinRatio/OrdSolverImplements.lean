module

public import MinCostFlow.MinRatio.OrdSolverReachInv
public import MinCostFlow.MinRatio.SolverInitWired
public import MinCostFlow.MinRatio.OrdChainRefreshWired
public import MinCostFlow.MinRatio.OrdFindCycleWired
public import MinCostFlow.MinRatio.ShiftLevelWired
public import MinCostFlow.Final.ForestConcretePrograms

/-!
# End-to-end `DSRep.Implements` for ordered Algorithm 2 (`minRatioMachineContractWithV`)

Assembles `solverStateRepInv_local`, `SolverInitStepSpec`, `solverOps_update_runs` (op `0`),
`solverOps_query_runs` (op `1`), and `solverOps_detect_runs` (op `2`) into a direct
`WordRAM.DSRep.Implements` proof for the representation `solverStateRepInv` (`solverStateRep`
with the reachable-state invariant `OrdSolverReachInv`, `MinRatio/OrdSolverReachInv.lean`) against `minRatioMachineContractWithV` for
`Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / 2^k)`, parameterized by
`Rcore : DSRep (SparseCoreOrdAbs cfg.T)`, and specializes it directly to the target signature
of `Final.DyadicWithVConcretePrograms.supported`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore.Program Scaling Scaling.Machine Final

/-- What `ordSolver_implements_minRatioContractWithV` takes as a hypothesis, beyond the
inner specifications. Every other clause of the contract follows from the reachable-state
invariant `OrdSolverReachInv` of `solverStateRepInv`, or from `solverStateRep`.
- `Init`, `Query`, `Detect` and the `Update` space and cost clauses: the rate `rate m` and the
  space `alloc` dominate the bounds of the operations.
The numeric budget after `Update` is not here: `solverTreeNumericInv_of_update` proves it. -/
@[expose] def OrdSolverContractEnvelope {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    (G : MGraph) (m V psi k epsExp initSpace initBudget findSpace findBudget
      shiftSpace shiftBudget maxEdges maxPaths : ℕ)
    (refreshSpace refreshBudget : ℕ → ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (rate : ℕ → ℕ) (alloc : ℕ → List ℕ → ℕ) : Prop :=
  let L := F.limbs
  let P := F.fmt.precision
  let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
  let C := minRatioMachineContractWithV F
    (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
    G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc
  -- Init
  (∀ args mem, C.initPre args mem →
    initSpace ≤ alloc 3 args ∧ initBudget ≤ rate m * (m + 1)) ∧
  -- Op 0 (`Update`)
  (∀ root batch g l eta heap mem model tok,
    Rrep.rep root model tok mem → OrdSolverReachInv G P model tok →
    C.pre 0 model [root, batch, g, l, eta, heap] mem →
    (∀ a, Rrep.foot root tok a → a < heap) →
    (∀ U, BatchAt mem batch U →
      let model1 := alg2PreLoopState cfg model U (readVector mem g 4 L P m) (readVector mem l 4 L P m)
      let N := shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain
      updateSpaceBound L m cfg.P.d model.nextFresh U.length (loopStepBound cfg model1) findSpace
        shiftSpace maxEdges maxPaths (refreshSpace U.length) + 2 ≤ alloc 0 [root, batch, g, l, eta, heap] ∧
      updateBudgetBound L cfg.P.d G.n tok.intCap model.nextFresh U.length N findBudget shiftBudget
        maxEdges maxPaths (detectOffTreeDrainUnit L) (refreshBudget U.length) ≤
        rate m * (1 + mem batch) ∧
      ∀ i ≤ cfg.P.d,
        shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i < 2 ^ w)) ∧
  -- Op 1 (`Query`)
  (∀ root e heap mem model tok,
    Rrep.rep root model tok mem → OrdSolverReachInv G P model tok →
    C.pre 1 model [root, e, heap] mem →
    max (L + LinkCut.PathProg.pathAlloc L 4 tok.tree.n
        [tok.treeHeap, mem (tok.slots + model.extToInt e), heap + L])
      (2 + 5 * L) + L ≤ alloc 1 [root, e, heap] ∧
    pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 53 * L + 160 ≤ rate m) ∧
  -- Op 2 (`Detect`)
  (∀ root heap mem model tok,
    Rrep.rep root model tok mem → OrdSolverReachInv G P model tok →
    C.pre 2 model [root, heap] mem →
    1 + m + ((algorithm2_detect cfg model).1.card + 1) * detectTreeRoundSpace L +
      tok.offReadyCount * (2 + 4 * L) ≤ alloc 2 [root, heap] ∧
    ((algorithm2_detect cfg model).1.card + 1) * (detectTreeStepBudget L model.extG.n + 2) + 200 ≤
      rate m * (1 + (algorithm2_detect cfg model).1.card))

/-- With `0 < ε ≤ 2^E` and a length of at least `2^(-E)`, the detector threshold lies in
`[0, 2^(P + 2E + 1)]`. The lower bound is `detectorThreshold_pos`. The upper bound is
`detectorThreshold_scaled_bound` times `2^P`. -/
theorem detectorThreshold_mem_range {P E : ℕ} {ε len : ℝ} (hε : 0 < ε) (hεE : ε ≤ (2 : ℝ) ^ E)
    (hlen : (2 : ℝ) ^ (-(E : ℤ)) ≤ len) :
    0 ≤ detectorThreshold P ε len ∧ detectorThreshold P ε len ≤ (2 : ℤ) ^ (P + 2 * E + 1) := by
  have hl : 1 / (2 : ℝ) ^ E ≤ len := by rwa [zpow_neg, zpow_natCast, ← one_div] at hlen
  have hlenPos : 0 < len := lt_of_lt_of_le (by positivity) hl
  refine ⟨(detectorThreshold_pos P ε len hε hlenPos).le, ?_⟩
  have hp : (0 : ℝ) < 2 ^ P := by positivity
  have hsc := detectorThreshold_scaled_bound P E ε len hεE hl
  rw [div_le_iff₀ hp, ← pow_add] at hsc
  have : ((detectorThreshold P ε len : ℤ) : ℝ) ≤ (((2 : ℤ) ^ (P + 2 * E + 1) : ℤ) : ℝ) := by
    push_cast; rw [show P + 2 * E + 1 = 2 * E + 1 + P by omega]; exact hsc
  exact_mod_cast this

/-- The numeric budget after `Update`. The tree budget `B, R` that `solverOps_update_runs`
returns is at most `B_bound + X, R_bound + X` with `X = maxPaths · 2^(3E + 2 + P)`. Raise it to
these bounds (`PathTreeNumericInv.mono`). The capacity premise is then `hcapTreeB`, since the
tree has `n = G.n` vertices. Each new length is at least `2^(-E)` (the `Update` precondition), so
its threshold is at most `2^(P + 2E + 1) ≤ B_bound` (`detectorThreshold_mem_range`, `hthrB`).
The negated threshold fits, since twice the threshold is below the capacity. -/
theorem solverTreeNumericInv_of_update {cfg : Alg2Config} {L P n E : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {B R B_bound R_bound X : ℤ}
    (hεPos : 0 < cfg.ε) (hεE : cfg.ε ≤ (2 : ℝ) ^ E)
    (htn : tok.tree.n = n) (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hB : B ≤ B_bound + X) (hR : R ≤ R_bound + X)
    (hcap : 2 * ((2 * n + 1 : ℕ) : ℤ) * ((B_bound + X) + (R_bound + X)) <
      (Num.capacity 4 L : ℤ))
    (hX : 0 ≤ X) (hthrB : (2 : ℤ) ^ (P + 2 * E + 1) ≤ B_bound)
    (hlen : ∀ e ∈ model.extG.E, (2 : ℝ) ^ (-(E : ℤ)) ≤ model.extℓ e) :
    SolverTreeNumericInv P model tok := by
  have hnum' := hnum.mono hB hR
  have hRm : 0 ≤ R_bound + X := le_trans hnum.2.1 hR
  have hthr (e : ℕ) (he : e ∈ model.extG.E) :
      0 ≤ detectorThreshold P cfg.ε (model.extℓ e) ∧
        detectorThreshold P cfg.ε (model.extℓ e) ≤ B_bound + X := by
    obtain ⟨h0, h1⟩ := detectorThreshold_mem_range (P := P) hεPos hεE (hlen e he)
    exact ⟨h0, by linarith⟩
  have hk : (1 : ℤ) ≤ ((2 * n + 1 : ℕ) : ℤ) := by push_cast; omega
  refine ⟨B_bound + X, R_bound + X, hnum', htn ▸ hcap, fun e he => ?_, fun e he => ?_⟩
  · rw [abs_of_nonneg (hthr e he).1]; exact (hthr e he).2
  · obtain ⟨h0, h1⟩ := hthr e he
    have hsum : (B_bound + X) + (R_bound + X) ≤
        ((2 * n + 1 : ℕ) : ℤ) * ((B_bound + X) + (R_bound + X)) :=
      le_mul_of_one_le_left (by linarith) hk
    constructor <;> linarith [Num.capacity 4 L]

/-- End-to-end `DSRep.Implements` theorem for `solverStateRepInv` (the representation
`solverStateRep` with the reachable-state invariant `OrdSolverReachInv`) and the bundled
deterministic procedures `solverOpsProcs` against `minRatioMachineContractWithV` of
`Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / 2^k)`, parameterized by
`Rcore : DSRep (SparseCoreOrdAbs cfg.T)`. `Init` makes the invariant true and each operation
keeps it: the model facts by `ordSolverReachBase_init`, `ordSolverReachBase_update` and
`ordSolverReachBase_detect`, the numeric budget by `SolverInitStepSpec`, by `solverTreeNumericInv_of_update`
for `Update` (with `hεLe` and `hthrB`), and by `solverOps_query_runs` and `solverOps_detect_runs`.
The invariant `OrdSolverReachInv` here does not give `Chain.Ordered.ShiftLoopChainInv` of the chain
that the shift loop starts from, so this theorem takes it as the hypothesis `hLoopInv`.
`ordSolver_implements_full_credit` (`OrdSolverImplementsFull.lean`) proves it from
`OrdSolverReached`. -/
theorem ordSolver_implements_minRatioContractWithV
    {w base initProc chainRefreshProc findCycleProc shiftLevelProc m U_cap V psi k epsExp
      capExp limbMul capLimit
      initSpace initBudget findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {p : Program} {B_bound R_bound : ℤ}
    {refreshSpace refreshBudget : ℕ → ℕ} {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ}
    (hw : 14 ≤ w) (hfmt4 : F.fmt.limbBits = 4) (hLpos : 0 < F.limbs)
    (hPL : F.fmt.precision ≤ 4 * F.limbs)
    (hmPos : 0 < m) (hεPos : 0 < cfg.ε) (hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent)
    (hthrB : (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_bound)
    (hα : cfg.α = Num.IPM.alphaPrime m U_cap / 8)
    (hepsExp : epsExp = k + Num.IPM.alphaExponent m U_cap + 10)
    (hGE : ∀ e < m, e ∈ G.E)
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
    (hCapFacts : ∀ model : Alg2State cfg, OrdSolverReachBase G model →
      WireCapFacts capExp limbMul F.limbs capLimit model)
    (hV : cfg.ValidOrdNoHidden)
    (hLoopInv : ∀ model : Alg2State cfg, OrdSolverReachBase G model →
      ∀ (U : List Update) (g l : ℕ → ℝ),
        Chain.Ordered.ShiftLoopChainInv cfg (alg2PreLoopState cfg model U g l).chain)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc))
    (hInit : SolverInitStepSpec F cfg G m V psi k epsExp Rcore p initProc initSpace initBudget)
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
    (hEnv : OrdSolverContractEnvelope F cfg G m V psi k epsExp initSpace initBudget
      findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths refreshSpace refreshBudget
      Rcore rate alloc) :
    (solverStateRepInv cfg G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore).Implements w p initProc (solverOpsDispatch base)
      (minRatioMachineContractWithV F
        (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
        G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc) := by
  let L := F.limbs
  let P := F.fmt.precision
  obtain ⟨hEnvInit, hEnv0, hEnv1, hEnv2⟩ := hEnv
  refine ⟨solverStateRepInv_local cfg G L P m V psi k epsExp (detectOffTreeDrainUnit L) hlocalCore,
    ?_, ?_⟩
  · -- Init
    intro args mem pos ω hargsW hpre hz hroom
    obtain ⟨hspLe, hcostLe⟩ := hEnvInit args mem hpre
    obtain ⟨body, hbody, hInitRun⟩ := hInit
    obtain ⟨finalHeap, cost, out, tok, hr, hfits, hrep, _, hnum, hresp, hcost⟩ :=
      hInitRun args mem pos ω hargsW hpre hz (by dsimp only [minRatioMachineContractWithV, minRatioMachineContractAt] at hroom; omega)
    have hlPos : ∀ e ∈ G.E,
        0 < readVector mem (args.getD 2 0) F.fmt.limbBits L P m e := by
      obtain ⟨graph, g, l, heap, hargsEq, _, _, _, _, _, _, _, _, _, _, _, hlpos, _⟩ := hpre
      subst hargsEq
      exact hlpos
    refine ⟨body, hbody, .returned finalHeap, out, cost, hr,
      (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).init G
        (readVector mem (args.getD 1 0) F.fmt.limbBits L P m)
        (readVector mem (args.getD 2 0) F.fmt.limbBits L P m),
      tok, ⟨hrep, ordSolverReachBase_init cfg G _ _ hlPos, hnum⟩, ⟨rfl, hfits⟩,
      ⟨hresp.1, hresp.2.1.trans (Nat.add_le_add_left hspLe _), hresp.2.2.1, hresp.2.2.2.1, hresp.2.2.2.2⟩,
      hcost.trans hcostLe⟩
  · -- Operations `0` (Update), `1` (Query), `2` (Detect)
    intro i root model tok args mem pos ω hargsW hhead hrepI hpre hbelow hz hroom
    obtain ⟨hrep, hinv⟩ := hrepI
    obtain ⟨hbase, hnumInv⟩ := hinv
    obtain ⟨hextEq, hlen, hBr⟩ := hbase
    obtain ⟨hcapPos, hnfLe, _⟩ := solverStateRep_intCap hrep
    have htn : tok.tree.n = G.n := (solverStateRep_tree_n hrep).trans (by rw [hextEq])
    match i with
    | 0 =>
      have hpre0 := hpre
      obtain ⟨_, handle_, batch, g, l, eta, heap, U0, hargsEq, _, _, _, hBU0, _, hRefU0, _, _, _,
        _, _, _, _, _, hglIn, _, _⟩ := hpre
      subst hargsEq
      have hrEq : handle_ = root := by simpa using hhead
      cases hrEq
      have hheapArg : heapArg [root, batch, g, l, eta, heap] = heap := rfl
      rw [hheapArg] at hbelow hz hroom
      obtain hUBounds :=
        hEnv0 root batch g l eta heap mem model tok hrep ⟨⟨hextEq, hlen, hBr⟩, hnumInv⟩
          hpre0 hbelow
      have hroomU : ∀ U, BatchAt mem batch U →
          let model1 := alg2PreLoopState cfg model U (readVector mem g 4 F.limbs F.fmt.precision m) (readVector mem l 4 F.limbs F.fmt.precision m)
          heap + updateSpaceBound F.limbs m cfg.P.d model.nextFresh U.length (loopStepBound cfg model1)
            findSpace shiftSpace maxEdges maxPaths (refreshSpace U.length) + 2 < 2 ^ w := fun U hBU => by
        have hsp := (hUBounds U hBU).1
        simp only [minRatioMachineContractWithV, minRatioMachineContractAt, L, P] at hroom hsp ⊢
        omega
      obtain ⟨body, hbody, ret, cost, out, model', tok', hr, hpost, hrep', _hintCap', hz', hretLo,
          hretAndCost, hframe', hfoot', B', R', hnum', hB', hR'⟩ :=
        solverOps_update_runs (w := w) (base := base) (chainRefreshProc := chainRefreshProc)
          (findCycleProc := findCycleProc) (shiftLevelProc := shiftLevelProc)
          (m := m) (U_cap := U_cap) (V := V) (psi := psi) (k := k) (epsExp := epsExp)
          (capExp := capExp) (limbMul := limbMul) (capLimit := capLimit)
          (findSpace := findSpace) (findBudget := findBudget)
          (shiftSpace := shiftSpace) (shiftBudget := shiftBudget)
          (maxEdges := maxEdges) (maxPaths := maxPaths)
          (root := root) (batch := batch) (g := g) (l := l) (eta := eta) (heap := heap) (pos := pos)
          (F := F) (cfg := cfg) (G := G) hlocalCore hw hfmt4 hV hPL hα hepsExp hp
          hRefresh hFind hShift hBridge hrep (hCapFacts model ⟨hextEq, hlen, hBr⟩) hpre0 hextEq hBr hbelow hGE hz
          hmPos hcapPos hnfLe h5L1W hdW hepsW hpsiLimW h2nW hlogW
          hsizeM hmaxEP hcapEvalB hcapTreeB hcapOffB hroomU (fun U hBU => (hUBounds U hBU).2.2)
          (fun U _ => hLoopInv model ⟨hextEq, hlen, hBr⟩ U _ _)
      have hbase' : OrdSolverReachBase G model' := by
        obtain ⟨actual, _, _, _, hres⟩ := hpost
        rw [(hres U0 hBU0).1]
        refine ordSolverReachBase_update ⟨hextEq, hlen, hBr⟩ hRefU0 fun e he => ?_
        exact lt_of_lt_of_le (by positivity) (hglIn e he).2.1
      have hnumStep : SolverTreeNumericInv P model' tok' := by
        obtain ⟨actual, _, _, _, hres⟩ := hpost
        have hl' : model'.extℓ = readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m := by
          rw [(hres U0 hBU0).1]; exact (ordAlg2_update_ext cfg _ model U0 _ _ _).2
        refine solverTreeNumericInv_of_update (E := F.rangeExponent) (n := G.n) hεPos hεLe
          ((solverStateRep_tree_n hrep').trans (by rw [hbase'.1])) hnum' hB' hR' hcapTreeB
          (mul_nonneg (Int.natCast_nonneg _) (pow_nonneg (by norm_num) _)) hthrB fun e he => ?_
        rw [hl']
        exact (hglIn e (hbase'.1 ▸ he)).2.1
      obtain ⟨hretHi, hcostHi⟩ := hretAndCost U0 hBU0
      obtain ⟨hspDom, hcostDom, _⟩ := hUBounds U0 hBU0
      refine ⟨body, hbody, .returned ret, out, cost, hr, model', tok',
        ⟨hrep', hbase', hnumStep⟩, hpost,
        ⟨hretLo, by
          rw [hheapArg]
          simp only [Outcome.value, minRatioMachineContractWithV, minRatioMachineContractAt] at hretHi hspDom ⊢
          omega,
         hz', hframe', hfoot'⟩,
        ?_⟩
      have hget1 : [root, batch, g, l, eta, heap].getD 1 0 = batch := rfl
      dsimp only [solverStateRepInv]
      simp only [minRatioMachineContractWithV, minRatioMachineContractAt, hget1] at hcostHi hcostDom ⊢
      omega
    | 1 =>
      have hpre0 := hpre
      obtain ⟨_, handle_, e, heap, hargsEq, _⟩ := hpre
      subst hargsEq
      have hrEq : handle_ = root := by simpa using hhead
      cases hrEq
      have hheapArg : heapArg [root, e, heap] = heap := rfl
      rw [hheapArg] at hbelow hz hroom
      obtain ⟨hspDom, hcostDom⟩ :=
        hEnv1 root e heap mem model tok hrep ⟨⟨hextEq, hlen, hBr⟩, hnumInv⟩ hpre0
      obtain ⟨hfits, hfitsExp⟩ := hnumInv.fits hrep
      obtain ⟨body, hbody, ret, cost, out, tok', hr, hpost, hrep', _, _, hz', hretLo, hretHi,
          hframe', hfoot', hcostHi, hkeep, _⟩ :=
        solverOps_query_runs (w := w) (base := base) (chainRefreshProc := chainRefreshProc)
          (findCycleProc := findCycleProc) (shiftLevelProc := shiftLevelProc)
          (m := m) (V := V) (psi := psi) (k := k) (epsExp := epsExp)
          (root := root) (e := e) (heap := heap) (pos := pos)
          (F := F) (cfg := cfg) (G := G) (κ := 1 / (2 : ℝ) ^ k) (α := cfg.α)
          hlocalCore hw hfmt4 hp hrep hpre0 hextEq hbelow hz (htn ▸ h2nW) (htn ▸ hlogW)
          hfits hfitsExp
          (by simp only [minRatioMachineContractWithV, minRatioMachineContractAt] at hroom; omega)
      have htn' : tok'.tree.n = tok.tree.n :=
        (solverStateRep_tree_n hrep').trans (solverStateRep_tree_n hrep).symm
      obtain ⟨B, R, hnB, hcapB, hthrB, hfitB⟩ := hnumInv
      refine ⟨body, hbody, .returned ret, out, cost, hr, model, tok',
        ⟨hrep', ⟨hextEq, hlen, hBr⟩, B, R, hkeep B R hnB, htn' ▸ hcapB, hthrB, hfitB⟩,
        hpost,
        ⟨hretLo, by
          rw [hheapArg]
          simp only [Outcome.value, minRatioMachineContractWithV, minRatioMachineContractAt]
          omega,
         hz', hframe', hfoot'⟩,
        ?_⟩
      dsimp only [solverStateRepInv]
      simp only [minRatioMachineContractWithV, minRatioMachineContractAt, Nat.mul_one]
      omega
    | 2 =>
      have hpre0 := hpre
      obtain ⟨_, handle_, heap, hargsEq⟩ := hpre
      subst hargsEq
      have hrEq : handle_ = root := by simpa using hhead
      cases hrEq
      have hheapArg : heapArg [root, heap] = heap := rfl
      rw [hheapArg] at hbelow hz hroom
      obtain ⟨hspDom, hcostDom⟩ :=
        hEnv2 root heap mem model tok hrep ⟨⟨hextEq, hlen, hBr⟩, hnumInv⟩ hpre0
      obtain ⟨B, R, hnum, hcapB, hthrB, hfitNeg⟩ := hnumInv
      obtain ⟨body, hbody, ret, cost, out, tok', hr, hpost, hrep', _, _, hnum', hz', hretLo, hretHi,
          hframe', hfoot', hcostHi, _⟩ :=
        solverOps_detect_runs (w := w) (base := base) (chainRefreshProc := chainRefreshProc)
          (findCycleProc := findCycleProc) (shiftLevelProc := shiftLevelProc)
          (m := m) (V := V) (psi := psi) (k := k) (epsExp := epsExp)
          (root := root) (heap := heap) (pos := pos)
          (F := F) (cfg := cfg) (G := G) (κ := 1 / (2 : ℝ) ^ k) (α := cfg.α)
          hlocalCore hw hfmt4 hLpos hp (fun e he => hextEq ▸ hGE e he) hεPos hlen hnum hcapB
          hthrB hfitNeg hrep hpre0 hbelow hz (htn ▸ h2nW) (htn ▸ hlogW)
          (by simp only [minRatioMachineContractWithV, minRatioMachineContractAt] at hroom; omega)
      have htn' : tok'.tree.n = tok.tree.n :=
        (solverStateRep_tree_n hrep').trans (solverStateRep_tree_n hrep).symm
      refine ⟨body, hbody, .returned ret, out, cost, hr, (algorithm2_detect cfg model).2, tok',
        ⟨hrep', ordSolverReachBase_detect ⟨hextEq, hlen, hBr⟩,
          B, R, hnum', htn' ▸ hcapB, hthrB, hfitNeg⟩,
        hpost,
        ⟨hretLo, by
          rw [hheapArg]
          simp only [Outcome.value, minRatioMachineContractWithV, minRatioMachineContractAt]
          omega,
         hz', hframe', hfoot'⟩,
        ?_⟩
      dsimp only [solverStateRepInv]
      simp only [minRatioMachineContractWithV, minRatioMachineContractAt,
        Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith]
      omega
    | i + 3 =>
      exact False.elim hpre.2

/-- Exact `Final.DyadicWithVConcretePrograms.supported`-shaped instantiation theorem:
produces the existential `DSRep` and `Implements` witness required by
`MinCostFlow.Final.DyadicWithVConcretePrograms.supported` for any fixed deterministic `cycle`
embedding `solverOpsProcs` at `base`, any chain witness `W` given by the caller, and any
`Rcore : DSRep (SparseCoreOrdAbs cfg.T)`. -/
theorem ordSolver_supported_for_dyadicWithV
    (lastTool : LastLevelTool) (lastConstant : ℝ)
    (lastSpec : lastTool.IsSpec (SparseCore.lastLevelParams lastConstant))
    (W : Final.ConcreteChainWitnessWithLast lastTool lastConstant lastSpec)
    (cycleInit base chainRefreshProc findCycleProc shiftLevelProc : ℕ)
    (cycle : List Stmt) (cycleRate : ℕ → ℕ)
    (cycleAllocation : ℕ → ℕ → ℕ → List ℕ → ℕ) (cycleSpace : ℕ → ℕ → ℕ)
    (allocationCoefficient allocationDegree : ℕ)
    (source J : Scaling.Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (_hCost : J.CostsBounded (J.m ^ 10))
    (hCap : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (Final.concreteEdgeThresholdWithLast
          W)
        (Final.concreteQualityBudgetWithLast
          W)
        (solverConnectedAugmented J).m) ≤
      wordSize (scratchWordMultiplier 1
        (Final.forestProgramsScratchDegree allocationCoefficient allocationDegree
          (Final.concreteQualityLinearCoeff
            (Final.concreteEdgeThresholdWithLast
              W)
            (Final.concreteQualityBudgetWithLast
              W))))
        source.solverWords) :
    let threshold := Final.concreteEdgeThresholdWithLast W
    let A := Final.concreteQualityBudgetWithLast W
    let Ck := Final.concreteQualityLinearCoeff threshold A
    let deg := Final.forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent threshold A I.m
    let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
    let dispatch := Final.mrdsSolverDispatch cycleInit (solverOpsDispatch base) cycle.length
    let forest := Final.dynLctForestBodies 4 (Final.mrdsCycleBase + cycle.length)
    let p := Final.linkedCappedSolverProgramWithV threshold A dispatch cycle forest
    let cfg := Final.concreteCirculationCfgWithLast W J
    let F := ipmQualityMinRatioFormat I.m V k hw
    ∀ (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (psi epsExp capExp limbMul capLimit
        initSpace initBudget findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths : ℕ)
      (refreshSpace refreshBudget : ℕ → ℕ) (B_bound R_bound : ℤ),
      Rcore.Local →
      epsExp = k + Num.IPM.alphaExponent I.m V + 10 →
      5 * F.limbs + 1 < 2 ^ w →
      cfg.P.d + 1 < 2 ^ w → epsExp < 2 ^ w →
      ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ < 2 ^ w →
      2 * (namedInstance I).n + 1 < 2 ^ w →
      Nat.log 2 (2 * (namedInstance I).n + 1) ≤ 4 * F.limbs →
      Nat.size I.m ≤ F.rangeExponent + 8 →
      maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20) →
      2 * (((maxEdges + maxPaths * (namedInstance I).n : ℕ) : ℤ) * B_bound) <
        (Num.capacity 4 F.limbs : ℤ) →
      2 * ((2 * (namedInstance I).n + 1 : ℕ) : ℤ) *
        ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision)) +
          (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision))) <
        (Num.capacity 4 F.limbs : ℤ) →
      B_bound + (2 : ℤ) ^ (3 * F.rangeExponent + 2 + F.fmt.precision) <
        (Num.capacity 4 F.limbs : ℤ) →
      (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_bound →
      (∀ model : Alg2State cfg, OrdSolverReachBase (namedInstance I) model →
        WireCapFacts capExp limbMul F.limbs capLimit model) →
      cfg.ValidOrdNoHidden →
      (∀ model : Alg2State cfg, OrdSolverReachBase (namedInstance I) model →
        ∀ (U : List Update) (g l : ℕ → ℝ),
          Chain.Ordered.ShiftLoopChainInv cfg (alg2PreLoopState cfg model U g l).chain) →
      p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc) →
      SolverInitStepSpec F cfg (namedInstance I) I.m V psi k epsExp Rcore p cycleInit initSpace initBudget →
      ChainRefreshStepSpecW w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p chainRefreshProc refreshSpace
        refreshBudget 0 0 B_bound R_bound →
      FindCycleStepSpecW w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p findCycleProc findSpace
        findBudget maxEdges maxPaths →
      ShiftLevelStepSpecW w F.limbs F.fmt.precision I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p shiftLevelProc shiftSpace
        shiftBudget 0 0 →
      GoodCycleNumericBridge F cfg (namedInstance I) I.m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) Rcore maxEdges maxPaths B_bound R_bound →
      OrdSolverContractEnvelope F cfg (namedInstance I) I.m V psi k epsExp initSpace initBudget
        findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths refreshSpace refreshBudget
        Rcore cycleRate (cycleAllocation I.n I.m) →
      (∀ j < 4, ∀ args, cycleAllocation I.n I.m j args ≤ cycleSpace I.n I.m) →
      ∃ RC : DSRep (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).State,
        RC.Implements w p cycleInit (solverOpsDispatch base)
          (minRatioMachineContractWithV F
            (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) (namedInstance I) I.m V
            (1 / (2 : ℝ) ^ k) (Num.IPM.alphaPrime I.m V / 8)
            cycleRate (cycleAllocation I.n I.m)) ∧
        (∀ j < 4, ∀ args, cycleAllocation I.n I.m j args ≤ cycleSpace I.n I.m) := by
  intro threshold A Ck deg I V k w dispatch forest p cfg F
    Rcore psi epsExp capExp limbMul capLimit initSpace initBudget findSpace findBudget shiftSpace shiftBudget
    maxEdges maxPaths refreshSpace refreshBudget B_bound R_bound
    hlocalCore hepsExp h5L1W hdW hepsW hpsiLimW h2nW hlogW hsizeM hmaxEP hcapEvalB hcapTreeB hcapOffB hthrB
    hCapFacts hV hLoopInv hp hInit hRefresh hFind hShift hBridge hEnv hAllocLe
  have hfit := ipm_quality_parameter_words_fit I.m V k hw
  have hw14 : 14 ≤ w := hfit.1
  have hImPos : 0 < I.m :=
    lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm (fun e => (hCap e).1)).1
  have hLpos : 0 < F.limbs := by
    dsimp only [F, ipmQualityMinRatioFormat, ipmQualityLimbs]; omega
  have hPL : F.fmt.precision ≤ 4 * F.limbs := by
    dsimp only [F, ipmQualityMinRatioFormat, ipmQualityPrecision, ipmQualityLimbs]; omega
  have hεPos : 0 < cfg.ε := by
    dsimp only [cfg, Final.concreteCirculationCfgWithLast, Final.concreteCirculationCfgOfDims,
      Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
    positivity
  have hαEq : cfg.α = Num.IPM.alphaPrime I.m V / 8 := rfl
  have hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent := by
    dsimp only [cfg, Final.concreteCirculationCfgWithLast, Final.concreteCirculationCfgOfDims,
      Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
    have hk : (1 : ℝ) / 2 ^ k ≤ 1 := div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    have ha : (1 : ℝ) / 2 ^ Num.IPM.alphaExponent I.m V ≤ 1 :=
      div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)
    have hprod := mul_le_one₀ hk (by positivity) ha
    have hE : (1 : ℝ) ≤ 2 ^ F.rangeExponent := one_le_pow₀ (by norm_num)
    have hpos : (0 : ℝ) ≤ 1 / 2 ^ k * (1 / 2 ^ Num.IPM.alphaExponent I.m V) := by positivity
    linarith
  refine ⟨solverStateRepInv cfg (namedInstance I) F.limbs F.fmt.precision I.m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore, ?_, hAllocLe⟩
  exact ordSolver_implements_minRatioContractWithV (U_cap := V) hlocalCore hw14 rfl hLpos hPL
    hImPos hεPos hεLe hthrB hαEq hepsExp (fun e he => Finset.mem_range.mpr he) h5L1W hdW hepsW hpsiLimW h2nW hlogW hsizeM hmaxEP hcapEvalB hcapTreeB hcapOffB
    hCapFacts hV hLoopInv hp hInit hRefresh hFind hShift hBridge hEnv

end MinCostFlow.MinRatio
