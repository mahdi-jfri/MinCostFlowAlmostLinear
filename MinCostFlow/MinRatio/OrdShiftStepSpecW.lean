module

public import MinCostFlow.MinRatio.WireSpecBase
public import MinCostFlow.Chain.Ordered.ShiftLoopLevels

/-!
# Wired credit-bearing level-shift contract (`ShiftLevelStepSpecW`)

Defines `ShiftLevelStepSpecW`, the corrected credit-bearing contract for `shiftLevelWiredBody`
extending `ShiftLevelStepSpecCredit` with the `OffTreeRecBound`, `WireCapFacts`, and
`∀ j < cfg.P.d, model.chain.bran j < cfg.P.k` premises and the `tok'.intCap` and
`OffTreeRecBound` conclusions (`OrdChainWireAdapters.lean` proves `shiftLevelStepSpecW_wired`).
It also assumes `Chain.Ordered.ShiftLoopChainInv` of the chain, which the loop of `Update` keeps
(`updateCycleLoop_ind_credit`), and the bounds `hlogW` and `hcapTree` of the loop. From these the
term step gets its reached-state facts (`shiftTerm_reached_facts_1_to_9`), and the deep shift
under the layout contract needs them too.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program

/-- Wired credit-bearing level-shift contract matching `ShiftTermChainSyncSpecW` and
`ShiftDeepChainSyncSpecW`: extends `ShiftLevelStepSpecCredit` with the `OffTreeRecBound`,
`WireCapFacts`, and `bran j < k` premises and the `tok'.intCap` and `OffTreeRecBound`
conclusions. -/
@[expose] def ShiftLevelStepSpecW (w L P m V psi k epsExp drainUnit capExp limbMul capLimit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftLevelProc shiftSpace shiftFixed toolMul treeMul : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftLevelProc]? = some body ∧
    ∀ (root heap pos : ℕ) (i : Fin (cfg.P.d + 1)) (ω : ℕ → Bool) (mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      let model' := alg2LoopShiftStep cfg model i
      (model.chain.shiftCount i.val : ℝ) + 1 ≤
        gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val →
      (if i.val < cfg.P.d then model.chain.bran i.val else model.branD) < cfg.P.k →
      (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
      shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val < 2 ^ w →
      model.passes i + 1 < 2 ^ w →
      Rrep.rep root model tok mem →
      Chain.Ordered.ShiftLoopChainInv cfg model.chain →
      Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem tok.edgeRecords B →
      OffTreeRecBound model L mem tok.edgeRecords B →
      WireCapFacts capExp limbMul L capLimit model →
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + shiftSpace < 2 ^ w →
      ∃ nextHeap cost out tok',
        Runs w p ω body (startState [root, i.val, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + shiftSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧ tok'.intCap = tok.intCap ∧
        Rrep.rep root model' tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
        OffTreeRecBound model' L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤
          shiftFixed +
            toolMul * (model'.chain.totalRuntime - model.chain.totalRuntime) +
            treeMul * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
            Rrep.phi root tok mem

end MinCostFlow.MinRatio
