module

public import MinCostFlow.MinRatio.OrdSolverImplements
public import MinCostFlow.MinRatio.OrdSolverRepFullKFBL
public import MinCostFlow.MinRatio.OrdSolverUpdateClauses
public import MinCostFlow.MinRatio.OrdSolverQuotaFit
public import MinCostFlow.MinRatio.OrdShiftLoopLevels
import Mathlib.Tactic

/-!
# `DSRep.Implements` for the one representation `solverStateRepFull`

`ordSolver_implements_minRatioContractWithV` (`OrdSolverImplements.lean`) proves the contract
for `solverStateRepInv`, whose potential does not pay for the shift loop. Here the representation
is `solverStateRepFull` (`OrdSolverRepFull.lean`). Its potential holds:
* `B` times the unused shift quota, the shift deposit, and the forward potential
  (`B = cycleLoopIterBudget …`), paying for the shift loop;
* `toolMul * runtimeCredit` and `treeMul * treeCredit` (`OrdSolverToolCredit.lean`), paying for
  sparse-core tool cost rises (`Δ totalRuntime`) and chain-tree edge updates (`Δ totalTreeUpdates`)
  across `Init`, `ChainRefresh`, and `ShiftLevel`.

Main definitions and theorems:
* `OrdSolverContractEnvelopeFullCredit`: rate, space, and reached-state quota-word-fit envelope
  with dual credit charges `toolMul, treeMul`.
* `OrdSolverContractEnvelopeFull`: the `toolMul = 0, treeMul = 0` specialization.
* `ordSolver_implements_full_credit`: full `DSRep.Implements` theorem for `solverStateRepFull`
  with credit-bearing `Init`, `ChainRefresh`, and `ShiftLevel` step specs.
* `ordSolver_implements_full`: specialization of `ordSolver_implements_full_credit` at
  `toolMul = 0, treeMul = 0` for fixed-budget step specs.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore.Program Scaling Scaling.Machine Final

/-- A number in `[2^{-E}, 2^E]` has a logarithm of absolute value at most `E`, since
`log 2 ≤ 1`. -/
theorem abs_log_le_of_two_pow_bounds {E : ℕ} {x : ℝ} (h1 : (2 : ℝ) ^ (-(E : ℤ)) ≤ x)
    (h2 : x ≤ (2 : ℝ) ^ E) : |Real.log x| ≤ E := by
  have hpos : 0 < x := lt_of_lt_of_le (by positivity) h1
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hE : (0 : ℝ) ≤ E := Nat.cast_nonneg E
  have hup : Real.log x ≤ E * Real.log 2 := by
    have := Real.log_le_log hpos h2
    rwa [Real.log_pow] at this
  have hlo : -(E * Real.log 2) ≤ Real.log x := by
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_zpow] at this
    push_cast at this
    linarith
  rw [abs_le]
  constructor <;> nlinarith

/-- Rate and space envelope for `ordSolver_implements_full_credit`, including the initial and
per-update dual credit charges (`toolMul`, `treeMul`). The shift-quota word-fit clause is
discharged automatically from `MinRatioDetectedWith.stages_le` (`OrdSolverQuotaFit.lean`). -/
@[expose] def OrdSolverContractEnvelopeFullCredit {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    (G : MGraph) (m V psi k epsExp initSpace initBudget findSpace findBudget
      shiftSpace shiftBudget maxEdges maxPaths toolMul treeMul : ℕ)
    (refreshSpace refreshBudget : ℕ → ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (rate : ℕ → ℕ) (alloc : ℕ → List ℕ → ℕ) : Prop :=
  let L := F.limbs
  let P := F.fmt.precision
  let B := cycleLoopIterBudget L cfg.P.d findBudget shiftBudget
  let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
  let C := minRatioMachineContractWithV F
    (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
    G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc
  -- Init
  (∀ args mem, C.initPre args mem →
    initSpace ≤ alloc 3 args ∧
    initBudget + B * ((cfg.P.d + 1) *
      ⌊(10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)⌋₊) +
      toolMul * chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0) +
      treeMul * chainRebuildCap cfg (treeUpdateFactorNat cfg) (fun _ => 0) ≤ rate m * (m + 1)) ∧
  -- Op 0 (`Update`)
  (∀ root batch g l eta heap mem model tok,
    Rrep.rep root model tok mem → OrdSolverReachedInv (1 / (2 : ℝ) ^ k) G P model tok →
    C.pre 0 model [root, batch, g, l, eta, heap] mem →
    (∀ a, Rrep.foot root tok a → a < heap) →
    (∀ U, BatchAt mem batch U →
      let model1 := alg2PreLoopState cfg model U (readVector mem g 4 L P m) (readVector mem l 4 L P m)
      updateSpaceBound L m cfg.P.d model.nextFresh U.length (loopStepBound cfg model1) findSpace
        shiftSpace maxEdges maxPaths (refreshSpace U.length) + 2 ≤ alloc 0 [root, batch, g, l, eta, heap] ∧
      updateBudgetNoLoop L G.n tok.intCap model.nextFresh U.length maxEdges maxPaths
          (detectOffTreeDrainUnit L) (refreshBudget U.length) + B +
        B * fwdWeight cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) 0 * U.length +
        updateCreditCharge cfg toolMul treeMul U ≤
        rate m * (1 + mem batch))) ∧
  -- Op 1 (`Query`)
  (∀ root e heap mem model tok,
    Rrep.rep root model tok mem → OrdSolverReachedInv (1 / (2 : ℝ) ^ k) G P model tok →
    C.pre 1 model [root, e, heap] mem →
    max (L + LinkCut.PathProg.pathAlloc L 4 tok.tree.n
        [tok.treeHeap, mem (tok.slots + model.extToInt e), heap + L])
      (2 + 5 * L) + L ≤ alloc 1 [root, e, heap] ∧
    pathTreeBudget LinkCut.PathProg.pathC L model.extG.n + 53 * L + 160 ≤ rate m) ∧
  -- Op 2 (`Detect`)
  (∀ root heap mem model tok,
    Rrep.rep root model tok mem → OrdSolverReachedInv (1 / (2 : ℝ) ^ k) G P model tok →
    C.pre 2 model [root, heap] mem →
    1 + m + ((algorithm2_detect cfg model).1.card + 1) * detectTreeRoundSpace L +
      tok.offReadyCount * (2 + 4 * L) ≤ alloc 2 [root, heap] ∧
    ((algorithm2_detect cfg model).1.card + 1) * (detectTreeStepBudget L model.extG.n + 2) + 200 ≤
      rate m * (1 + (algorithm2_detect cfg model).1.card))

/-- Specialization of `OrdSolverContractEnvelopeFullCredit` at `toolMul = 0, treeMul = 0` for
fixed-budget step specs. -/
@[expose] def OrdSolverContractEnvelopeFull {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    (G : MGraph) (m V psi k epsExp initSpace initBudget findSpace findBudget
      shiftSpace shiftBudget maxEdges maxPaths : ℕ)
    (refreshSpace refreshBudget : ℕ → ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (rate : ℕ → ℕ) (alloc : ℕ → List ℕ → ℕ) : Prop :=
  OrdSolverContractEnvelopeFullCredit F cfg G m V psi k epsExp initSpace initBudget findSpace
    findBudget shiftSpace shiftBudget maxEdges maxPaths 0 0 refreshSpace refreshBudget Rcore
    rate alloc

/-- Credit-bearing `DSRep.Implements` theorem for `solverStateRepFullKFBL`, paying for sparse-core
tool-cost rises (`toolMul * Δ totalRuntime`) and chain-tree edge updates
(`treeMul * Δ totalTreeUpdates`) via dual ghost credits, while maintaining
`SolverLevelCapsInv` and `DeepInv` for `ShiftLevelStepSpecWKFBL`. -/
theorem ordSolver_implements_full_credit
    {w base initProc chainRefreshProc findCycleProc shiftLevelProc m U_cap V psi k epsExp
      capExp limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap
      initSpace initBudget findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths
      toolMul treeMul : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {DeepInv : ChainState cfg.T cfg.P → Prop}
    {p : Program} {B_bound R_bound : ℤ}
    {refreshSpace refreshBudget : ℕ → ℕ} {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ}
    (hMono : toolMul = 0 ∨ ToolCostMono cfg.T)
    (hV : cfg.ValidOrdNoHidden) (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ)
    (hw : 14 ≤ w) (hfmt4 : F.fmt.limbBits = 4) (hLpos : 0 < F.limbs)
    (hPL : F.fmt.precision ≤ 4 * F.limbs)
    (hmPos : 0 < m) (hεPos : 0 < cfg.ε) (hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent)
    (hthrB : (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_bound)
    (hα : cfg.α = Num.IPM.alphaPrime m U_cap / 8)
    (hepsExp : epsExp = k + Num.IPM.alphaExponent m U_cap + 10)
    (hGE : ∀ e < m, e ∈ G.E)
    (h5L1W : 5 * F.limbs + 1 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) (hepsW : epsExp < 2 ^ w)
    (hQuotaBoundW : (2 * G.m + 2) *
      shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) < 2 ^ w)
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
    (hCapLevels : ∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ capLimit →
      SparseCoreCapHyp capExp limbMul F.limbs (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap)
    (hIntCapMax : initTargetCap cfg G ≤ intCapMax)
    (hFEdgeCap : 2 * G.n ≤ forestEdgeCap)
    (hDeepInv : DeepShiftChainInvHyps w F cfg G k wordExp stretchPrec DeepInv)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc))
    (hInit : SolverInitStepSpecCreditKFBL F cfg G m V psi k epsExp Rcore p initProc initSpace
      initBudget toolMul treeMul)
    (hRefresh : ChainRefreshStepSpecWKFBL w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit G.n (initTargetCap cfg G) cfg Rcore
      p chainRefreshProc refreshSpace refreshBudget toolMul treeMul B_bound R_bound)
    (hFind : FindCycleStepSpecW w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p findCycleProc findSpace
      findBudget maxEdges maxPaths)
    (hShift : ShiftLevelStepSpecWKFBL w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap G.n (initTargetCap cfg G) cfg Rcore p shiftLevelProc shiftSpace shiftBudget
      toolMul treeMul)
    (hBridge : GoodCycleNumericBridge F cfg G m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore maxEdges maxPaths B_bound R_bound)
    (hEnv : OrdSolverContractEnvelopeFullCredit F cfg G m V psi k epsExp initSpace initBudget
      findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths toolMul treeMul
      refreshSpace refreshBudget Rcore rate alloc) :
    (solverStateRepFullKFBL cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) (cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget)
      toolMul treeMul Rcore DeepInv).Implements w p initProc (solverOpsDispatch base)
      (minRatioMachineContractWithV F
        (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
        G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc) := by
  obtain ⟨hEnvInit, hEnv0, hEnv1, hEnv2⟩ := hEnv
  refine ⟨solverStateRepFullKFBL_local cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k epsExp
    (detectOffTreeDrainUnit F.limbs) (cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget)
    toolMul treeMul hlocalCore DeepInv, ?_, ?_⟩
  · -- Init
    intro args mem pos ω hargsW hpre hz hroom
    obtain ⟨hspLe, hcostLe⟩ := hEnvInit args mem hpre
    obtain ⟨body, hbody, hInitRun⟩ := hInit
    obtain ⟨finalHeap, cost, out, tok, hr, hfits, hrep, hcapsInit, hcapInit, hnum, hresp, hcost⟩ :=
      hInitRun args mem pos ω hargsW hpre hz (by dsimp only [minRatioMachineContractWithV, minRatioMachineContractAt] at hroom; omega)
    have hinitLens :
        (∀ e ∈ G.E, 0 < readVector mem (args.getD 2 0) F.fmt.limbBits F.limbs F.fmt.precision m e) ∧
        LengthsWithin G F.rangeExponent
          (readVector mem (args.getD 2 0) F.fmt.limbBits F.limbs F.fmt.precision m) := by
      obtain ⟨graph, g, l, heap, hargsEq, _, _, _, _, _, _, _, _, _, _, _, hlpos, hwithin, _⟩ := hpre
      subst hargsEq
      exact ⟨hlpos, hwithin⟩
    have hlPos := hinitLens.1
    have hwithin := hinitLens.2
    have hGridInit : ∀ e ∈ G.E, ∃ q : ℤ,
        (q : ℝ) / (2 : ℝ) ^ F.fmt.precision =
          readVector mem (args.getD 2 0) F.fmt.limbBits F.limbs F.fmt.precision m e := by
      intro e _
      unfold readVector
      split_ifs
      · exact ⟨Num.intVal mem (args.getD 2 0 + e * F.limbs) F.fmt.limbBits F.limbs, rfl⟩
      · exact ⟨0, by simp⟩
    have hGV : G.IsValid := by
      obtain ⟨graph, g, l, heap, _, _, _, _, _, _, hGV, _⟩ := hpre
      exact hGV
    set s0 := Ordered.algorithm2_init cfg G
      (readVector mem (args.getD 1 0) F.fmt.limbBits F.limbs F.fmt.precision m)
      (readVector mem (args.getD 2 0) F.fmt.limbBits F.limbs F.fmt.precision m)
    have hDeep0 : DeepInv s0.chain := hDeepInv.init _ _ hwithin hGridInit
    have hreach : OrdSolverReached cfg (1 / (2 : ℝ) ^ k) G s0 :=
      ordSolverReached_init cfg (1 / (2 : ℝ) ^ k) G _ _ hGV hlPos
        (fun e he => (abs_log_le_of_two_pow_bounds (hwithin e he).1 (hwithin e he).2).trans hEΨ)
    obtain ⟨hRtCap0, hTuCap0⟩ := hreach.runtime_and_tree_le_cap hV hmG hnG
    obtain ⟨hrepS, hphiLe⟩ := solverStateRepFull_phi_init_le (κ := 1 / (2 : ℝ) ^ k) (G := G)
      (unit := (cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget))
      (toolMul := toolMul) (treeMul := treeMul) hrep
    refine ⟨body, hbody, .returned finalHeap, out, cost, hr, s0,
      ((tok, 0), (runtimeCredit cfg s0, treeCredit cfg s0)),
      ⟨⟨hrepS, ⟨⟨ordSolverReachBase_init cfg G _ _ hlPos, hnum⟩, hreach,
        hreach.nextFresh_le hV hmG hnG, hcapInit⟩, rfl, rfl⟩, hcapsInit, hDeep0⟩, ⟨rfl, hfits⟩,
      ⟨hresp.1, hresp.2.1.trans (Nat.add_le_add_left hspLe _), hresp.2.2.1, hresp.2.2.2.1, hresp.2.2.2.2⟩,
      ?_⟩
    have hcost' : cost + (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) Rcore).phi (heapArg args) tok out.mem ≤
        initBudget + toolMul * s0.chain.totalRuntime + treeMul * s0.chain.totalTreeUpdates := hcost
    have hinitAmort : cost + ((solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) Rcore).phi (heapArg args) tok out.mem +
        toolMul * runtimeCredit cfg s0 + treeMul * treeCredit cfg s0) ≤
        initBudget + toolMul * chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0) +
          treeMul * chainRebuildCap cfg (treeUpdateFactorNat cfg) (fun _ => 0) :=
      wire_dual_credit_init_step cfg G
        (readVector mem (args.getD 1 0) F.fmt.limbBits F.limbs F.fmt.precision m)
        (readVector mem (args.getD 2 0) F.fmt.limbBits F.limbs F.fmt.precision m)
        hcost' hRtCap0 hTuCap0
    have hphiLe' : (solverStateRepFull cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) (cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget)
        toolMul treeMul Rcore).phi (heapArg args) ((tok, 0), (runtimeCredit cfg s0, treeCredit cfg s0)) out.mem ≤
        (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
          (detectOffTreeDrainUnit F.limbs) Rcore).phi (heapArg args) tok out.mem +
        (cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget) *
          ((cfg.P.d + 1) * Nat.floor ((10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1))) +
        toolMul * runtimeCredit cfg s0 + treeMul * treeCredit cfg s0 := hphiLe
    refine le_trans ?_ hcostLe
    change cost + (solverStateRepFull cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) (cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget)
      toolMul treeMul Rcore).phi (heapArg args) ((tok, 0), (runtimeCredit cfg s0, treeCredit cfg s0)) out.mem ≤ _
    omega
  · -- Operations `0` (Update), `1` (Query), `2` (Detect)
    intro i root model tok args mem pos ω hargsW hhead hrepFK hpre hbelow hz hroom
    obtain ⟨hrepF, hCaps, hDeep⟩ := hrepFK
    obtain ⟨hrepS, hfull, hrcG, htcG⟩ := hrepF
    obtain ⟨hrep, hfwd, hghost⟩ := hrepS
    obtain ⟨hinv, hreach, hnfB, hintCapB⟩ := hfull
    obtain ⟨hbase, hnumInv⟩ := hinv
    obtain ⟨hextEq, hlen, hBr⟩ := hbase
    obtain ⟨hcapPos, hnfLe, _⟩ := solverStateRep_intCap hrep
    have htn : tok.1.1.tree.n = G.n := (solverStateRep_tree_n hrep).trans (by rw [hextEq])
    have hphi : (solverStateRepFullKFBL cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k epsExp
        (detectOffTreeDrainUnit F.limbs) (cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget)
        toolMul treeMul Rcore DeepInv).phi root tok mem = _ :=
      solverStateRepFullKFBL_phi_eq ⟨hrep, hfwd, hghost⟩ hrcG htcG
    match i with
    | 0 =>
      have hpre0 := hpre
      obtain ⟨_, handle_, batch, g, l, eta, heap, U0, hargsEq, _, _, _, hBU0, _, hRefU0, _, _, _,
        _, _, _, _, _, hglIn, hU0Le, hdet⟩ := hpre
      subst hargsEq
      have hrEq : handle_ = root := by simpa using hhead
      cases hrEq
      have hheapArg : heapArg [root, batch, g, l, eta, heap] = heap := rfl
      rw [hheapArg] at hbelow hz hroom
      obtain hUBounds :=
        hEnv0 root batch g l eta heap mem model tok.1.1 hrep
          ⟨⟨⟨hextEq, hlen, hBr⟩, hnumInv⟩, hreach, hnfB, hintCapB⟩
          hpre0 hbelow
      have hroomU : ∀ U, BatchAt mem batch U →
          let model1 := alg2PreLoopState cfg model U (readVector mem g 4 F.limbs F.fmt.precision m) (readVector mem l 4 F.limbs F.fmt.precision m)
          heap + updateSpaceBound F.limbs m cfg.P.d model.nextFresh U.length (loopStepBound cfg model1)
            findSpace shiftSpace maxEdges maxPaths (refreshSpace U.length) + 2 < 2 ^ w := fun U hBU => by
        have hsp := (hUBounds U hBU).1
        simp only [minRatioMachineContractWithV, minRatioMachineContractAt] at hroom hsp ⊢
        omega
      have hpsiLimW : ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ < 2 ^ w :=
        lt_of_le_of_lt (ceil_two_mul_alg2PsiGame_le_quotaBound cfg G.m) hQuotaBoundW
      have hCapModel : WireCapFacts capExp limbMul F.limbs capLimit model := by
        obtain ⟨D, η, op, T, hHist, hE, hL, hG, hm⟩ := hreach
        have hInv := ((Ordered.algorithm2_uncond_preserves_with (η := η) (1 / (2 : ℝ) ^ k) hV hHist
          hE hL (fun t ht => by rw [hG t ht]; exact hmG)
          (fun t ht => by rw [hG t ht]; exact hnG)).1 T le_rfl).1
        rw [← hm] at hInv
        intro j hj vCap eCap hlim
        rw [hInv.hLvlM, hInv.hN0]
        exact hCapLevels j hj vCap eCap hlim
      have hquotasW : ∀ U, BatchAt mem batch U →
          let model1 := alg2PreLoopState cfg model U
            (readVector mem g 4 F.limbs F.fmt.precision m) (readVector mem l 4 F.limbs F.fmt.precision m)
          ∀ i ≤ cfg.P.d,
            shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i < 2 ^ w :=
        fun U _ i hi => lt_of_le_of_lt (detectedWith_preLoop_shiftQuota_le hdet U _ _ hi) hQuotaBoundW
      have hLoopInv : ∀ U, BatchAt mem batch U →
          Chain.Ordered.ShiftLoopChainInv cfg (alg2PreLoopState cfg model U
            (readVector mem g 4 F.limbs F.fmt.precision m)
            (readVector mem l 4 F.limbs F.fmt.precision m)).chain := by
        intro U hBU
        obtain rfl := batchAt_unique_of_refresh hRefU0 hBU0 hBU
        have h := hreach.preLoop_shiftLoopChainInv hV hmG hnG hConn hRefU0
          (fun e he => lt_of_lt_of_le (by positivity) (hglIn e he).2.1)
          (fun e he => (abs_log_le_of_two_pow_bounds (hglIn e he).2.1 (hglIn e he).2.2).trans hEΨ)
          (fun e he hnot => ordAlg2_detectedWith_agree hdet e he fun ⟨u, hu, hi⟩ => hnot u hu hi)
        rwa [hfmt4] at h
      have hmLeGm : m ≤ G.m := by
        have hsub : Finset.range m ⊆ G.E := fun e he => hGE e (Finset.mem_range.mp he)
        simpa [MGraph.m] using Finset.card_le_card hsub
      have hNoGrow : ∀ U, BatchAt mem batch U → model.nextFresh + U.length ≤ tok.1.1.intCap := by
        intro U hBU
        obtain rfl := batchAt_unique_of_refresh hRefU0 hBU0 hBU
        unfold initTargetCap at hintCapB
        omega
      obtain ⟨body, hbody, ret, cost, out, model', tok', hr, hpost, hrep', hCaps', hDeep', hintCap',
          hz', hretLo, hretAndCost, hframe', hfoot', B', R', hnum', hB', hR'⟩ :=
        solverOps_update_runs_credit_kfbl (w := w) (base := base) (chainRefreshProc := chainRefreshProc)
          (findCycleProc := findCycleProc) (shiftLevelProc := shiftLevelProc)
          (m := m) (U_cap := U_cap) (V := V) (psi := psi) (k := k) (epsExp := epsExp)
          (capExp := capExp) (limbMul := limbMul) (capLimit := capLimit)
          (wordExp := wordExp) (stretchPrec := stretchPrec) (intCapMax := intCapMax)
          (forestEdgeCap := forestEdgeCap) (vCap := G.n) (eCap := initTargetCap cfg G)
          (findSpace := findSpace) (findBudget := findBudget)
          (shiftSpace := shiftSpace) (shiftBudget := shiftBudget)
          (maxEdges := maxEdges) (maxPaths := maxPaths) (toolMul := toolMul) (treeMul := treeMul)
          (root := root) (batch := batch) (g := g) (l := l) (eta := eta) (heap := heap) (pos := pos)
          (F := F) (cfg := cfg) (G := G) (DeepInv := DeepInv)
          hlocalCore hMono hw hfmt4 hV hPL hα hepsExp hp
          hRefresh hFind hShift hBridge hFEdgeCap
          (fun U gVec lVec hU hLen hGrid hAg hD =>
            hDeepInv.preLoop model U gVec lVec hreach hextEq hU hLen hGrid hAg hD)
          hDeepInv.shift hDeepInv.toModel hrep hCaps hDeep (hintCapB.symm ▸ hIntCapMax) hNoGrow
          hCapModel hpre0 hextEq hBr hbelow hGE hz hmPos hcapPos hnfLe h5L1W hdW hepsW hpsiLimW
          h2nW hlogW hsizeM hmaxEP hcapEvalB hcapTreeB hcapOffB hroomU hquotasW hLoopInv
      obtain ⟨actual, _, _, _, hres⟩ := hpost
      have hm' : model' = ((Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).update
          model U0 (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
          (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) actual).1 := (hres U0 hBU0).1
      -- the caller's vectors, and what the precondition says about them
      have hlpos : ∀ e ∈ G.E, 0 < readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m e :=
        fun e he => lt_of_lt_of_le (by positivity) (hglIn e he).2.1
      have hlR : ∀ e ∈ G.E,
          |Real.log (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m e)| ≤ cfg.Ψ :=
        fun e he => (abs_log_le_of_two_pow_bounds (hglIn e he).2.1 (hglIn e he).2.2).trans hEΨ
      have hagree : ∀ e ∈ G.E, (∀ u ∈ U0, ¬ u.Inserts e) →
          readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m e = model.extg e ∧
            readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m e = model.extℓ e :=
        fun e he hnot => ordAlg2_detectedWith_agree hdet e he fun ⟨u, hu, hi⟩ => hnot u hu hi
      have hPreFwd := hreach.preLoop_fwd hV hmG hnG hRefU0 hlpos hlR hagree
      have hreach' : OrdSolverReached cfg (1 / (2 : ℝ) ^ k) G model' := by
        rw [hm']
        exact ordSolverReached_update hreach actual hRefU0 hlpos hlR hagree
      obtain ⟨hRtBefore, hTuBefore⟩ := hreach.runtime_and_tree_le_cap hV hmG hnG
      obtain ⟨hRtAfter, hTuAfter⟩ := hreach'.runtime_and_tree_le_cap hV hmG hnG
      have hbase' : OrdSolverReachBase G model' := by
        rw [hm']
        refine ordSolverReachBase_update ⟨hextEq, hlen, hBr⟩ hRefU0 fun e he => ?_
        exact lt_of_lt_of_le (by positivity) (hglIn e he).2.1
      have hnumStep : SolverTreeNumericInv F.fmt.precision model' tok' := by
        have hl' : model'.extℓ = readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m := by
          rw [hm']; exact (ordAlg2_update_ext cfg _ model U0 _ _ _).2
        refine solverTreeNumericInv_of_update (E := F.rangeExponent) (n := G.n) hεPos hεLe
          ((solverStateRep_tree_n hrep').trans (by rw [hbase'.1])) hnum' hB' hR' hcapTreeB
          (mul_nonneg (Int.natCast_nonneg _) (pow_nonneg (by norm_num) _)) hthrB fun e he => ?_
        rw [hl']
        exact (hglIn e (hbase'.1 ▸ he)).2.1
      obtain ⟨hretHi, hcostHi⟩ := hretAndCost U0 hBU0
      obtain ⟨hspDom, hcostDom⟩ := hUBounds U0 hBU0
      -- the amortized cost (`update_fwd_amortized` + `wire_dual_credit_update_step`)
      have hg4 : readVector mem g 4 F.limbs F.fmt.precision m =
          readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m := by rw [hfmt4]
      have hl4 : readVector mem l 4 F.limbs F.fmt.precision m =
          readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m := by rw [hfmt4]
      rw [updateBudgetBound_eq, hm', hg4, hl4] at hcostHi
      have hfrInv : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh :=
        hrep.2.2.2.2.1
      have hcostShift : cost +
          ((solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp (detectOffTreeDrainUnit F.limbs) Rcore).phi
              root tok' out.mem +
            toolMul * model.chain.totalRuntime + treeMul * model.chain.totalTreeUpdates) +
          shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
              ((Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).update model U0
                (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
                (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) actual).1.chain *
            cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget ≤
          updateBudgetNoLoop F.limbs G.n tok.1.1.intCap model.nextFresh U0.length maxEdges maxPaths
              (detectOffTreeDrainUnit F.limbs) (refreshBudget U0.length) +
            (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
              (alg2PreLoopState cfg model U0
                (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
                (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m)).chain + 1) *
              cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget +
            ((solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp (detectOffTreeDrainUnit F.limbs) Rcore).phi
                root tok.1.1 mem +
              toolMul * ((Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).update model U0
                (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
                (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) actual).1.chain.totalRuntime +
              treeMul * ((Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).update model U0
                (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
                (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) actual).1.chain.totalTreeUpdates) := by
        omega
      have hA := update_fwd_amortized cfg (1 / (2 : ℝ) ^ k) model U0
        (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
        (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m)
        actual hcostShift hfwd hPreFwd
      dsimp only at hA
      obtain ⟨hamort, hfwd'⟩ := hA
      have hDual := wire_dual_credit_update_step cfg (1 / (2 : ℝ) ^ k) model U0
        (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
        (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m)
        actual
        (cost := cost)
        (phi := (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
            (detectOffTreeDrainUnit F.limbs) Rcore).phi root tok.1.1 mem +
          cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget *
            (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain +
              chainShiftDeposit cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain) +
          cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget *
            fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) model.chain)
        (phi' := (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp
            (detectOffTreeDrainUnit F.limbs) Rcore).phi root tok' out.mem +
          cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget *
            (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
                ((Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).update model U0
                  (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
                  (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) actual).1.chain +
              chainShiftDeposit cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀)
                ((Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).update model U0
                  (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
                  (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) actual).1.chain) +
          cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget *
            fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg)
              ((Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)).update model U0
                (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision m)
                (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision m) actual).1.chain)
        (fixed := updateBudgetNoLoop F.limbs G.n tok.1.1.intCap model.nextFresh U0.length
            maxEdges maxPaths (detectOffTreeDrainUnit F.limbs) (refreshBudget U0.length) +
          cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget +
          cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget *
            fwdWeight cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) 0 * U0.length)
        (toolMul := toolMul) (treeMul := treeMul)
        hfrInv (hextEq ▸ hRefU0.1) hfwd hPreFwd hRtBefore hTuBefore
        (hm' ▸ hRtAfter) (hm' ▸ hTuAfter) (by omega)
      dsimp only at hDual
      have hrepS' : (solverStateRepShift cfg F.limbs F.fmt.precision m V psi k epsExp (detectOffTreeDrainUnit F.limbs) (cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget)
          Rcore).rep root model'
          (tok', fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) model'.chain)
          out.mem :=
        ⟨hrep', by rw [hm']; exact hfwd', rfl⟩
      have hintCapEq' : tok'.intCap = initTargetCap cfg G := by
        rw [hintCap' U0 hBU0, ite_eq_right (by unfold initTargetCap at hintCapB; omega)]
        exact hintCapB
      refine ⟨body, hbody, .returned ret, out, cost, hr, model',
        ((tok', fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) model'.chain),
         (runtimeCredit cfg model', treeCredit cfg model')),
        ⟨⟨hrepS', ⟨⟨hbase', hnumStep⟩, hreach', hreach'.nextFresh_le hV hmG hnG, hintCapEq'⟩, rfl, rfl⟩,
          hCaps', hDeep'⟩,
        ⟨actual, by assumption, by assumption, by assumption, hres⟩,
        ⟨hretLo, by
          rw [hheapArg]
          simp only [Outcome.value, minRatioMachineContractWithV, minRatioMachineContractAt] at hretHi hspDom ⊢
          omega,
         hz', hframe', hfoot'⟩,
        ?_⟩
      rw [solverStateRepFullKFBL_phi_eq (tok := ((tok', _), _)) hrepS' rfl rfl, hphi, hm']
      have hget1 : [root, batch, g, l, eta, heap].getD 1 0 = batch := rfl
      simp only [minRatioMachineContractWithV, minRatioMachineContractAt, hget1] at hcostDom ⊢
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
        hEnv1 root e heap mem model tok.1.1 hrep
          ⟨⟨⟨hextEq, hlen, hBr⟩, hnumInv⟩, hreach, hnfB, hintCapB⟩ hpre0
      obtain ⟨hfits, hfitsExp⟩ := hnumInv.fits hrep
      obtain ⟨body, hbody, ret, cost, out, tok', hr, hpost, hrep', hpresQ, hcapQ, hz', hretLo, hretHi,
          hframe', hfoot', hcostHi, hkeep, _⟩ :=
        solverOps_query_runs (w := w) (base := base) (chainRefreshProc := chainRefreshProc)
          (findCycleProc := findCycleProc) (shiftLevelProc := shiftLevelProc)
          (m := m) (V := V) (psi := psi) (k := k) (epsExp := epsExp)
          (root := root) (e := e) (heap := heap) (pos := pos)
          (F := F) (cfg := cfg) (G := G) (κ := 1 / (2 : ℝ) ^ k) (α := cfg.α)
          hlocalCore hw hfmt4 hp hrep hpre0 hextEq hbelow hz (htn ▸ h2nW) (htn ▸ hlogW)
          hfits hfitsExp
          (by simp only [minRatioMachineContractWithV, minRatioMachineContractAt] at hroom; omega)
      have htn' : tok'.tree.n = tok.1.1.tree.n :=
        (solverStateRep_tree_n hrep').trans (solverStateRep_tree_n hrep).symm
      obtain ⟨B, R, hnB, hcapB, hthrB, hfitB⟩ := hnumInv
      have hrepS' : (solverStateRepShift cfg F.limbs F.fmt.precision m V psi k epsExp (detectOffTreeDrainUnit F.limbs) (cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget)
          Rcore).rep root model (tok', tok.1.2) out.mem := ⟨hrep', hfwd, hghost⟩
      have hCapsQ : SolverLevelCapsInv F.fmt.precision V G.n (initTargetCap cfg G) model tok' out.mem :=
        hpresQ.to_capsInv hCaps rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
          (fun _ _ => rfl) rfl
      refine ⟨body, hbody, .returned ret, out, cost, hr, model, ((tok', tok.1.2), tok.2),
        ⟨⟨hrepS', ⟨⟨⟨hextEq, hlen, hBr⟩, B, R, hkeep B R hnB, htn' ▸ hcapB, hthrB, hfitB⟩,
          hreach, hnfB, hcapQ.trans hintCapB⟩,
          hrcG, htcG⟩, hCapsQ, hDeep⟩,
        hpost,
        ⟨hretLo, by
          rw [hheapArg]
          simp only [Outcome.value, minRatioMachineContractWithV, minRatioMachineContractAt]
          omega,
         hz', hframe', hfoot'⟩,
        ?_⟩
      rw [solverStateRepFullKFBL_phi_eq (tok := ((tok', tok.1.2), tok.2)) hrepS' hrcG htcG, hphi]
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
        hEnv2 root heap mem model tok.1.1 hrep
          ⟨⟨⟨hextEq, hlen, hBr⟩, hnumInv⟩, hreach, hnfB, hintCapB⟩ hpre0
      obtain ⟨B, R, hnum, hcapB, hthrB, hfitNeg⟩ := hnumInv
      obtain ⟨body, hbody, ret, cost, out, tok', hr, hpost, hrep', hpresD, hcapD, hnum', hz', hretLo, hretHi,
          hframe', hfoot', hcostHi, _⟩ :=
        solverOps_detect_runs (w := w) (base := base) (chainRefreshProc := chainRefreshProc)
          (findCycleProc := findCycleProc) (shiftLevelProc := shiftLevelProc)
          (m := m) (V := V) (psi := psi) (k := k) (epsExp := epsExp)
          (root := root) (heap := heap) (pos := pos)
          (F := F) (cfg := cfg) (G := G) (κ := 1 / (2 : ℝ) ^ k) (α := cfg.α)
          hlocalCore hw hfmt4 hLpos hp (fun e he => hextEq ▸ hGE e he) hεPos hlen hnum hcapB
          hthrB hfitNeg hrep hpre0 hbelow hz (htn ▸ h2nW) (htn ▸ hlogW)
          (by simp only [minRatioMachineContractWithV, minRatioMachineContractAt] at hroom; omega)
      have htn' : tok'.tree.n = tok.1.1.tree.n :=
        (solverStateRep_tree_n hrep').trans (solverStateRep_tree_n hrep).symm
      have hch : (algorithm2_detect cfg model).2.chain = model.chain := rfl
      have hrcEq : runtimeCredit cfg (algorithm2_detect cfg model).2 = runtimeCredit cfg model := rfl
      have htcEq : treeCredit cfg (algorithm2_detect cfg model).2 = treeCredit cfg model := rfl
      have hrepS' : (solverStateRepShift cfg F.limbs F.fmt.precision m V psi k epsExp (detectOffTreeDrainUnit F.limbs) (cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget)
          Rcore).rep root (algorithm2_detect cfg model).2 (tok', tok.1.2) out.mem :=
        ⟨hrep', hch ▸ hfwd, hch ▸ hghost⟩
      have hCapsD : SolverLevelCapsInv F.fmt.precision V G.n (initTargetCap cfg G)
          (algorithm2_detect cfg model).2 tok' out.mem :=
        hpresD.to_capsInv hCaps rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
          (fun _ _ => rfl) rfl
      have hreach' := ordSolverReached_detect hreach
      refine ⟨body, hbody, .returned ret, out, cost, hr, (algorithm2_detect cfg model).2,
        ((tok', tok.1.2), tok.2),
        ⟨⟨hrepS', ⟨⟨ordSolverReachBase_detect ⟨hextEq, hlen, hBr⟩,
          B, R, hnum', htn' ▸ hcapB, hthrB, hfitNeg⟩, hreach', hnfB, hcapD.trans hintCapB⟩,
          hrcEq ▸ hrcG, htcEq ▸ htcG⟩, hCapsD, hch ▸ hDeep⟩,
        hpost,
        ⟨hretLo, by
          rw [hheapArg]
          simp only [Outcome.value, minRatioMachineContractWithV, minRatioMachineContractAt]
          omega,
         hz', hframe', hfoot'⟩,
        ?_⟩
      rw [solverStateRepFullKFBL_phi_eq (tok := ((tok', tok.1.2), tok.2)) hrepS' (hrcEq ▸ hrcG) (htcEq ▸ htcG), hphi, hch, hrcEq, htcEq]
      simp only [minRatioMachineContractWithV, minRatioMachineContractAt,
        Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith]
      omega
    | i + 3 =>
      exact False.elim hpre.2

/-- Specialization of `ordSolver_implements_full_credit` at `toolMul = 0, treeMul = 0` for
fixed-budget `Init`, `ChainRefresh`, and `ShiftLevel` step specs under `KFBL`. -/
theorem ordSolver_implements_full
    {w base initProc chainRefreshProc findCycleProc shiftLevelProc m U_cap V psi k epsExp
      capExp limbMul capLimit wordExp stretchPrec intCapMax forestEdgeCap
      initSpace initBudget findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {DeepInv : ChainState cfg.T cfg.P → Prop}
    {p : Program} {B_bound R_bound : ℤ}
    {refreshSpace refreshBudget : ℕ → ℕ} {rate : ℕ → ℕ} {alloc : ℕ → List ℕ → ℕ}
    (hV : cfg.ValidOrdNoHidden) (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ)
    (hw : 14 ≤ w) (hfmt4 : F.fmt.limbBits = 4) (hLpos : 0 < F.limbs)
    (hPL : F.fmt.precision ≤ 4 * F.limbs)
    (hmPos : 0 < m) (hεPos : 0 < cfg.ε) (hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent)
    (hthrB : (2 : ℤ) ^ (F.fmt.precision + 2 * F.rangeExponent + 1) ≤ B_bound)
    (hα : cfg.α = Num.IPM.alphaPrime m U_cap / 8)
    (hepsExp : epsExp = k + Num.IPM.alphaExponent m U_cap + 10)
    (hGE : ∀ e < m, e ∈ G.E)
    (h5L1W : 5 * F.limbs + 1 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) (hepsW : epsExp < 2 ^ w)
    (hQuotaBoundW : (2 * G.m + 2) *
      shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) < 2 ^ w)
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
    (hCapLevels : ∀ i < cfg.P.d, ∀ vCap eCap, vCap + eCap + 2 ≤ capLimit →
      SparseCoreCapHyp capExp limbMul F.limbs (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap)
    (hIntCapMax : initTargetCap cfg G ≤ intCapMax)
    (hFEdgeCap : 2 * G.n ≤ forestEdgeCap)
    (hDeepInv : DeepShiftChainInvHyps w F cfg G k wordExp stretchPrec DeepInv)
    (hp : p.HasAt base (solverOpsProcs base chainRefreshProc findCycleProc shiftLevelProc))
    (hInit : SolverInitStepSpecCreditKFBL F cfg G m V psi k epsExp Rcore p initProc initSpace
      initBudget 0 0)
    (hRefresh : ChainRefreshStepSpecWKFBL w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit G.n (initTargetCap cfg G) cfg Rcore
      p chainRefreshProc refreshSpace refreshBudget 0 0 B_bound R_bound)
    (hFind : FindCycleStepSpecW w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit cfg Rcore p findCycleProc findSpace
      findBudget maxEdges maxPaths)
    (hShift : ShiftLevelStepSpecWKFBL w F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap G.n (initTargetCap cfg G) cfg Rcore p shiftLevelProc shiftSpace shiftBudget
      0 0)
    (hBridge : GoodCycleNumericBridge F cfg G m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) Rcore maxEdges maxPaths B_bound R_bound)
    (hEnv : OrdSolverContractEnvelopeFull F cfg G m V psi k epsExp initSpace initBudget
      findSpace findBudget shiftSpace shiftBudget maxEdges maxPaths
      refreshSpace refreshBudget Rcore rate alloc) :
    (solverStateRepFullKFBL cfg (1 / (2 : ℝ) ^ k) G F.limbs F.fmt.precision m V psi k epsExp
      (detectOffTreeDrainUnit F.limbs) (cycleLoopIterBudget F.limbs cfg.P.d findBudget shiftBudget)
      0 0 Rcore DeepInv).Implements w p initProc (solverOpsDispatch base)
      (minRatioMachineContractWithV F
        (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
        G m V (1 / (2 : ℝ) ^ k) cfg.α rate alloc) :=
  ordSolver_implements_full_credit (U_cap := U_cap) hlocalCore (Or.inl rfl) hV hmG hnG hConn hEΨ
    hw hfmt4 hLpos hPL hmPos hεPos hεLe hthrB hα hepsExp hGE h5L1W hdW hepsW hQuotaBoundW h2nW hlogW
    hsizeM hmaxEP hcapEvalB hcapTreeB hcapOffB hCapLevels hIntCapMax hFEdgeCap hDeepInv hp hInit
    hRefresh hFind hShift hBridge hEnv

end MinCostFlow.MinRatio
