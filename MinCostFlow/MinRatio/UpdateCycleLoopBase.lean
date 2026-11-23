module

public import MinCostFlow.MinRatio.SolverRep
public import MinCostFlow.MinRatio.UpdateQuality
public import MinCostFlow.MinRatio.UpdateGoodApplyPaths
public import MinCostFlow.MinRatio.ExplicitEdgeLayout
public import MinCostFlow.MinRatio.OrdBranchesLt
import WordRAM.Tactic

/-!
# Definitions and shift-check subroutine for the `Update` cycle loop

Provides the deterministic shift-eligibility checker `shiftCheckBody` (wrapping
`shiftFailureChecks` from `ShiftGuards.lean`), the candidate-cycle descriptor layout
`CycleDescriptorAt`, the modular subroutine contracts `FindCycleStepSpec` and
`ShiftLevelStepSpec`, and the fixed deterministic loop body `updateCycleLoopBody`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- Deterministic shift-eligibility and quota check procedure taking
`[passBase, passLimit, dPlus1, countBase, quotaBase]`.
Returns `0` if `Chain.Ordered.algorithm2_loopWith` must fail, or `i + 1` if level `i` is selected to shift. -/
@[expose] def shiftCheckBody : Stmt :=
  .assign 21 (.reg 2) ;;
  shiftFailureChecks ;;
  .cond (.reg 2)
    (.ret (.bin .add (.reg 5) (.const 1)))
    (.ret (.const 0))

theorem shiftCheckBody_noRand : shiftCheckBody.NoRand := by
  simp [shiftCheckBody, shiftFailureChecks_noRand, Stmt.NoRand]

/-- Execution of `shiftCheckBody`: preserves memory identically and returns `0` on failure
or `i + 1` when `findEligibleLevel = some i` and `shiftCount[i] + 1 ≤ gameShiftBound`. -/
theorem shiftCheckBody_runs {w passBase countBase quotaBase pos : ℕ} {cfg : Alg2Config}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} (model : Alg2State cfg)
    (hTables : shiftCheckTablesAt mem passBase countBase quotaBase model)
    (hpEnd : passBase + cfg.P.d < 2 ^ w) (hcEnd : countBase + cfg.P.d < 2 ^ w)
    (hqEnd : quotaBase + cfg.P.d < 2 ^ w) (hdW : cfg.P.d + 1 < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    let psi := alg2PsiGame cfg.Ψ cfg.P.M₀
    let chosen := findEligibleLevel cfg.P.d psi model.passes
    let ret := chosen.elim 0 (fun i =>
      if (model.chain.shiftCount i.val : ℝ) + 1 ≤
          gameShiftBound cfg.P psi model.chain.rebuildCount i.val then i.val + 1 else 0)
    ∃ cost out,
      Runs w p ω shiftCheckBody
        (startState [passBase, ⌈2 * psi⌉₊, cfg.P.d + 1, countBase, quotaBase] mem pos)
        (.returned ret) out cost ∧
      cost ≤ 20 * (cfg.P.d + 1) + 50 ∧
      out.mem = mem := by
  dsimp only
  let psi := alg2PsiGame cfg.Ψ cfg.P.M₀
  have hpsi : 0 ≤ psi := le_trans (by norm_num) (alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀)
  let s0 := startState [passBase, ⌈2 * psi⌉₊, cfg.P.d + 1, countBase, quotaBase] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 21 (cfg.P.d + 1) }
  have r1 : Runs w p ω (.assign 21 (.reg 2)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨cfg.P.d + 1, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
  obtain ⟨mid, cF, hrF, hcF, hbit, hsel, hmemF, _, _⟩ :=
    shiftFailureChecks_runs (w := w) (ω := ω) (st := s1) cfg.P psi model.passes
      model.chain.rebuildCount model.chain.shiftCount hpsi hw1
      (by simp [s1, s0, startState]) (by simp [s1, s0, startState]) (by simp [s1])
      (by simp [s1, s0, startState]) (by simp [s1, s0, startState])
      hTables.1 hTables.2.1 hTables.2.2 hpEnd hcEnd hqEnd hdW
  cases hch : findEligibleLevel cfg.P.d psi model.passes with
  | none =>
    simp only [hch, Option.elim_none] at hbit ⊢
    have hrRet : Runs w p ω (.ret (.const 0)) mid (.returned 0) mid 2 :=
      runs_ret_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have hrCond : Runs w p ω (.cond (.reg 2) (.ret (.bin .add (.reg 5) (.const 1))) (.ret (.const 0)))
        mid (.returned 0) mid 4 :=
      runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, hbit], by simp only [↓reduceIte]; exact hrRet,
        by simp [Expr.size]⟩
    refine ⟨2 + (cF + 4 + 1) + 1, mid,
      runs_seq_iff.mpr (Or.inr ⟨s1, 2, cF + 4 + 1, r1,
        runs_seq_iff.mpr (Or.inr ⟨mid, cF, 4, hrF, hrCond, rfl⟩), rfl⟩),
      by omega, hmemF⟩
  | some i =>
    have hr5 : mid.regs 5 = i.val := hsel i hch
    by_cases hcap : (model.chain.shiftCount i.val : ℝ) + 1 ≤
        gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val
    · simp only [hch, Option.elim_some, psi, hcap, ↓reduceIte] at hbit ⊢
      have hi1W : i.val + 1 < 2 ^ w := lt_of_le_of_lt (Nat.succ_le_of_lt i.isLt) hdW
      have hrRet : Runs w p ω (.ret (.bin .add (.reg 5) (.const 1))) mid (.returned (i.val + 1)) mid 4 :=
        runs_ret_iff.mpr ⟨i.val + 1, by simp [Expr.eval, BinOp.eval, hr5, hw1, hi1W], rfl, rfl, rfl⟩
      have hrCond : Runs w p ω (.cond (.reg 2) (.ret (.bin .add (.reg 5) (.const 1))) (.ret (.const 0)))
          mid (.returned (i.val + 1)) mid 6 :=
        runs_cond_iff.mpr ⟨1, 4, by simp [Expr.eval, hbit],
          by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact hrRet, by simp [Expr.size]⟩
      refine ⟨2 + (cF + 6 + 1) + 1, mid,
        runs_seq_iff.mpr (Or.inr ⟨s1, 2, cF + 6 + 1, r1,
          runs_seq_iff.mpr (Or.inr ⟨mid, cF, 6, hrF, hrCond, rfl⟩), rfl⟩),
        by omega, hmemF⟩
    · simp only [hch, Option.elim_some, psi, hcap, ↓reduceIte] at hbit ⊢
      have hrRet : Runs w p ω (.ret (.const 0)) mid (.returned 0) mid 2 :=
        runs_ret_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hrCond : Runs w p ω (.cond (.reg 2) (.ret (.bin .add (.reg 5) (.const 1))) (.ret (.const 0)))
          mid (.returned 0) mid 4 :=
        runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, hbit], by simp only [↓reduceIte]; exact hrRet,
          by simp [Expr.size]⟩
      refine ⟨2 + (cF + 4 + 1) + 1, mid,
        runs_seq_iff.mpr (Or.inr ⟨s1, 2, cF + 4 + 1, r1,
          runs_seq_iff.mpr (Or.inr ⟨mid, cF, 4, hrF, hrCond, rfl⟩), rfl⟩),
        by omega, hmemF⟩

/-- One shift transition of `Chain.Ordered.algorithm2_loopWith` at level `i : Fin (cfg.P.d + 1)`. -/
@[expose] noncomputable def alg2LoopShiftStep (cfg : Alg2Config) (model : Alg2State cfg)
    (i : Fin (cfg.P.d + 1)) : Alg2State cfg :=
  let curB := if i.val < cfg.P.d then model.chain.bran i.val else model.branD
  let wrapped := (curB + 1) % cfg.P.k = 0
  let ch' := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
  let branD' := if i.val < cfg.P.d then 0 else (model.branD + 1) % cfg.P.k
  let passes' : Fin (cfg.P.d + 1) → ℕ := fun j =>
    if i < j then 0
    else if j = i then (if wrapped then model.passes i + 1 else model.passes i)
    else model.passes j
  { model with chain := ch', branD := branD', passes := passes' }

/-- One shift transition of the cycle loop preserves `BranchesLtK`. -/
theorem branchesLtK_shiftStep {cfg : Alg2Config} {model : Alg2State cfg}
    (hbr : BranchesLtK cfg model) (i : Fin (cfg.P.d + 1)) :
    BranchesLtK cfg (alg2LoopShiftStep cfg model i) := by
  refine ⟨algorithm1_shift_bran cfg.T cfg.L cfg.P model.chain i.val hbr.1, ?_⟩
  dsimp only [alg2LoopShiftStep]
  split_ifs
  · exact cfg.P.hk
  · exact Nat.mod_lt _ cfg.P.hk

/-- Semantic route agreement for a candidate cycle descriptor: `edges` (internal edge IDs)
and `paths` (0-based vertex pairs) decompose `(algorithm1_findCycle model.chain).1` into
disjoint off-tree and tree components with exact signed and absolute detector accounting. -/
@[expose] def CycleRouteAt {cfg : Alg2Config} (model : Alg2State cfg)
    (edges : List (ℕ × Bool)) (paths : List (ℕ × ℕ)) : Prop :=
  let C := (algorithm1_findCycle model.chain).1
  let F := model.chain.toTreeChain.chainTree
  (∀ x ∈ edges, x.1 ∈ (model.chain.G 0).E \ F.E) ∧
  (∀ p ∈ paths, p.1 < model.extG.n ∧ p.2 < model.extG.n ∧ F.Connected p.1 p.2) ∧
  (∀ e ∈ model.extG.E,
    let ei := model.extToInt e
    C ei = (edges.map (fun x => walkFlow [x] ei)).sum +
      (paths.map (fun p => walkFlow (F.forestPath p.1 p.2) ei)).sum ∧
    ∀ k : ℝ,
      |k * C ei| = |k * (edges.map (fun x => walkFlow [x] ei)).sum| +
        (paths.map (fun p => |k * walkFlow (F.forestPath p.1 p.2) ei|)).sum)

/-- Six-word candidate-cycle descriptor written at `descBase` by `findCycleProc`, exposing
the fixed-point inner product, nonnegative weighted length, explicit off-tree edges, and
cancellation-free tree paths of `Δ_ext = liftEdgeFn model.extG model.extToInt (algorithm1_findCycle model.chain).1`. -/
@[expose] def CycleDescriptorAt {cfg : Alg2Config} (model : Alg2State cfg) (L P : ℕ)
    (mem : ℕ → ℕ) (descBase nextHeap : ℕ) (inner norm : ℤ)
    (edges : List (ℕ × Bool)) (paths : List (ℕ × ℕ)) : Prop :=
  let Δ := liftEdgeFn model.extG model.extToInt (algorithm1_findCycle model.chain).1
  let innerPtr := mem descBase
  let normPtr := mem (descBase + 1)
  let edgesBase := mem (descBase + 2)
  let pathsBase := mem (descBase + 4)
  mem (descBase + 3) = edges.length ∧
  mem (descBase + 5) = paths.length ∧
  descBase + 6 ≤ nextHeap ∧
  descBase ≤ innerPtr ∧ descBase ≤ normPtr ∧ descBase ≤ edgesBase ∧ descBase ≤ pathsBase ∧
  innerPtr + L ≤ nextHeap ∧ normPtr + L ≤ nextHeap ∧
  edgesBase + 2 * edges.length ≤ nextHeap ∧ pathsBase + 2 * paths.length ≤ nextHeap ∧
  0 ≤ norm ∧
  PathIntAt mem innerPtr 4 L inner ∧ PathIntAt mem normPtr 4 L norm ∧
  model.extG.inner model.extg Δ = (inner : ℝ) / (2 : ℝ) ^ P ∧
  model.extG.lnorm model.extℓ Δ = (norm : ℝ) / (2 : ℝ) ^ P ∧
  ExplicitEdgesAt mem edgesBase edges ∧ PathEndpointsAt mem pathsBase paths ∧
  CycleRouteAt model edges paths

/-- Off-tree edge-record numeric and pairwise-disjointness invariant preserved across
`ChainRefresh`, `FindCycle`, and `ShiftLevel`. -/
@[expose] def OffTreeRecInv {cfg : Alg2Config} (model : Alg2State cfg) (L : ℕ)
    (mem : ℕ → ℕ) (edgeRecords : ℕ) (B : ℤ) : Prop :=
  (∀ e ∈ model.extG.E, model.extToInt e ∉ model.chain.toTreeChain.chainTree.E →
    ∀ val, PathEdgeAt mem (mem (edgeRecords + model.extToInt e)) 4 L (some val) →
      |val.detector| ≤ B) ∧
  (∀ e₁ ∈ model.extG.E, ∀ e₂ ∈ model.extG.E, e₁ ≠ e₂ →
    model.extToInt e₁ ∉ model.chain.toTreeChain.chainTree.E →
    model.extToInt e₂ ∉ model.chain.toTreeChain.chainTree.E →
    mem (edgeRecords + model.extToInt e₁) + (2 + 4 * L) ≤ mem (edgeRecords + model.extToInt e₂) ∨
    mem (edgeRecords + model.extToInt e₂) + (2 + 4 * L) ≤ mem (edgeRecords + model.extToInt e₁))

/-- Transport `OffTreeRecInv` across memory agreement on tag-13 pointers and tag-18 blocks. -/
theorem offTreeRecInv_of_agree {cfg : Alg2Config} {L P m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {root : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem₁ mem₂ : ℕ → ℕ} {B : ℤ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem₁)
    (hOff : OffTreeRecInv model L mem₁ tok.edgeRecords B)
    (hag : ∀ a, (tok.tag a = 13 ∨ tok.tag a = 18) → mem₂ a = mem₁ a) :
    OffTreeRecInv model L mem₂ tok.edgeRecords B := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hedgeAcc, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, t13, _, _, _, t1718, _⟩ := htags
  have hptr (e : ℕ) (he : e ∈ model.extG.E) :
      mem₂ (tok.edgeRecords + model.extToInt e) = mem₁ (tok.edgeRecords + model.extToInt e) :=
    hag _ (Or.inl (t13 _ (hedgeAcc.1 e he).1))
  refine ⟨fun e he hnot val hpa => ?_, fun e₁ he₁ e₂ he₂ hne hn₁ hn₂ => ?_⟩
  · rw [hptr e he] at hpa
    exact hOff.1 e he hnot val (hpa.congr fun x hx1 hx2 => by
      have hx : x = mem₁ (tok.edgeRecords + model.extToInt e) +
          (x - mem₁ (tok.edgeRecords + model.extToInt e)) := by omega
      rw [hx]; exact (hag _ (Or.inr ((t1718 e he).2 hnot _ (by omega)))).symm)
  · rw [hptr e₁ he₁, hptr e₂ he₂]
    exact hOff.2 e₁ he₁ e₂ he₂ hne hn₁ hn₂

/-- Modular contract for the candidate-cycle finder subroutine `findCycleProc [root, heap]`. -/
@[expose] def FindCycleStepSpec (w L P m V psi k epsExp drainUnit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (findCycleProc : ℕ) (findSpace findBudget maxEdges maxPaths : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[findCycleProc]? = some body ∧
    ∀ (root heap pos : ℕ) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      Rrep.rep root model tok mem →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + findSpace < 2 ^ w →
      ∃ nextHeap cost out tok' inner norm edges paths,
        Runs w p ω body (startState [root, heap] mem pos) (.returned nextHeap) out cost ∧
        heap + 6 ≤ nextHeap ∧ nextHeap ≤ heap + findSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧
        edges.length ≤ maxEdges ∧ paths.length ≤ maxPaths ∧
        (∀ x < 2 * edges.length, tok'.tag (out.mem (heap + 2) + x) = 0) ∧
        (∀ x < 2 * paths.length, tok'.tag (out.mem (heap + 4) + x) = 0) ∧
        (∀ a, tok'.tag a = 18 → a < heap) ∧
        CycleDescriptorAt model L P out.mem heap nextHeap inner norm edges paths ∧
        Rrep.rep root model tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤ findBudget + Rrep.phi root tok mem

/-- Modular contract for the level-shift subroutine `shiftLevelProc [root, i, heap]`. -/
@[expose] def ShiftLevelStepSpec (w L P m V psi k epsExp drainUnit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftLevelProc : ℕ) (shiftSpace shiftBudget : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftLevelProc]? = some body ∧
    ∀ (root heap pos : ℕ) (i : Fin (cfg.P.d + 1)) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      (model.chain.shiftCount i.val : ℝ) + 1 ≤
        gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val →
      (if i.val < cfg.P.d then model.chain.bran i.val else model.branD) < cfg.P.k →
      shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val < 2 ^ w →
      model.passes i + 1 < 2 ^ w →
      Rrep.rep root model tok mem →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + shiftSpace < 2 ^ w →
      ∃ nextHeap cost out tok',
        Runs w p ω body (startState [root, i.val, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + shiftSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧
        Rrep.rep root (alg2LoopShiftStep cfg model i) tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv (alg2LoopShiftStep cfg model i) L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤ shiftBudget + Rrep.phi root tok mem

/-- Credit-bearing contract for the level-shift subroutine `shiftLevelProc [root, i, heap]`,
allowing its cost to charge `toolMul` times the rise of `totalRuntime` and `treeMul` times the
rise of `totalTreeUpdates`. -/
@[expose] def ShiftLevelStepSpecCredit (w L P m V psi k epsExp drainUnit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftLevelProc : ℕ) (shiftSpace shiftFixed toolMul treeMul : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftLevelProc]? = some body ∧
    ∀ (root heap pos : ℕ) (i : Fin (cfg.P.d + 1)) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      let model' := alg2LoopShiftStep cfg model i
      (model.chain.shiftCount i.val : ℝ) + 1 ≤
        gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val →
      (if i.val < cfg.P.d then model.chain.bran i.val else model.branD) < cfg.P.k →
      shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val < 2 ^ w →
      model.passes i + 1 < 2 ^ w →
      Rrep.rep root model tok mem →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + shiftSpace < 2 ^ w →
      ∃ nextHeap cost out tok',
        Runs w p ω body (startState [root, i.val, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + shiftSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧
        Rrep.rep root model' tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          shiftFixed +
            toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem

theorem ShiftLevelStepSpec.toCredit {w L P m V psi k epsExp drainUnit : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {p : Program}
    {shiftLevelProc shiftSpace shiftBudget : ℕ}
    (h : ShiftLevelStepSpec w L P m V psi k epsExp drainUnit cfg Rcore p shiftLevelProc
      shiftSpace shiftBudget) :
    ShiftLevelStepSpecCredit w L P m V psi k epsExp drainUnit cfg Rcore p shiftLevelProc
      shiftSpace shiftBudget 0 0 := by
  obtain ⟨body, hbody, hrun⟩ := h
  refine ⟨body, hbody, fun root heap pos i ω mem model tok B R h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => ?_⟩
  obtain ⟨nh, c, out, tok', hr, hl, hh, hlev, hrep, hnum, hoff, hz, hfr, hft, hc⟩ :=
    hrun root heap pos i ω mem model tok B R h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  exact ⟨nh, c, out, tok', hr, hl, hh, hlev, hrep, hnum, hoff, hz, hfr, hft, by simpa using hc⟩

/-- Fixed deterministic inner loop of `Chain.Ordered.algorithm2_loopWith cfg (1 / 2^k)`.
Arguments: `[root, quotaBase, passLimit, qExp, descOut, heap]` (`reg 0 .. reg 5`).
Writes `foundBit ∈ {0, 1}` at `descOut`, the final cycle-descriptor pointer `curDesc` at
`descOut + 1`, and returns the final heap pointer. -/
@[expose] def updateCycleLoopBody (findCycleProc updateQualityProc shiftCheckProc shiftLevelProc : ℕ) :
    Stmt :=
  .assign 10 (.load (.reg 0)) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .assign 12 (.load (.bin .add (.reg 10) (.const 5))) ;;
  .assign 13 (.load (.bin .add (.reg 10) (.const 11))) ;;
  .assign 14 (.bin .add (.reg 13) (.const 1)) ;;
  .assign 15 (.bin .add (.reg 11) (.reg 14)) ;;
  .assign 16 (.const 1) ;;
  .assign 17 (.const 0) ;;
  .assign 18 (.reg 5) ;;
  .assign 20 (.reg 5) ;;
  .loop (.reg 16)
    (.assign 20 (.reg 18) ;;
     .call 18 findCycleProc [.reg 0, .reg 18] ;;
     .assign 22 (.load (.reg 20)) ;;
     .assign 23 (.load (.bin .add (.reg 20) (.const 1))) ;;
     .call 24 updateQualityProc [.reg 23, .reg 22, .reg 12, .reg 3, .reg 18] ;;
     .assign 18 (.bin .add (.reg 18) (.bin .add (.bin .mul (.const 5) (.reg 12)) (.const 1))) ;;
     .cond (.reg 24)
       (.assign 17 (.const 1) ;; .assign 16 (.const 0))
       (.call 25 shiftCheckProc [.reg 11, .reg 2, .reg 14, .reg 15, .reg 1] ;;
        .cond (.reg 25)
          (.assign 26 (.bin .sub (.reg 25) (.const 1)) ;;
           .call 18 shiftLevelProc [.reg 0, .reg 26, .reg 18])
          (.assign 17 (.const 0) ;; .assign 16 (.const 0)))) ;;
  .store (.reg 4) (.reg 17) ;;
  .store (.bin .add (.reg 4) (.const 1)) (.reg 20) ;;
  .ret (.reg 18)

theorem updateCycleLoopBody_noRand (findCycleProc updateQualityProc shiftCheckProc shiftLevelProc : ℕ) :
    (updateCycleLoopBody findCycleProc updateQualityProc shiftCheckProc shiftLevelProc).NoRand := by
  simp [updateCycleLoopBody, Stmt.NoRand]

/-- Per-iteration heap space reserved by `updateCycleLoopBody`. -/
@[expose] def cycleLoopIterSpace (L findSpace shiftSpace : ℕ) : ℕ :=
  findSpace + (5 * L + 1) + shiftSpace

/-- Per-iteration amortized step budget of `updateCycleLoopBody`. -/
@[expose] def cycleLoopIterBudget (L d findBudget shiftBudget : ℕ) : ℕ :=
  findBudget + 181 * L + 20 * (d + 1) + shiftBudget + 420

end MinCostFlow.MinRatio
