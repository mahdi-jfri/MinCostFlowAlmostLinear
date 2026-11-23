module

public import MinCostFlow.MinRatio.OrdShiftLoopLevels
public import MinCostFlow.MinRatio.SolverRep
import MinCostFlow.MinRatio.InitPathTreeChainHelpers

/-!
# Reached-state preconditions (1)–(9) of `ShiftTermChainSyncSpecWExt`

Under `Chain.Ordered.ShiftLoopChainInv cfg model.chain` and `solverStateRep.rep`, proves the
nine reached-state preconditions of `ShiftTermChainSyncSpecWExt` (`WireChainSpecs.lean`)
at `lastTreeCap = 2 * levelM cfg.TP cfg.P cfg.P.d`:
1. `model.chain.lastBran < model.chain.lastK` (`ChainInv.hLastBran`);
2. `model.chain.lastK < 2 ^ w` (from `Rterm.rep` and `Rrep.foot` below `heap < 2 ^ w`);
3. `Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L` (passed through);
4. `2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < Num.capacity 4 L` (passed through);
5. `model'.chain.toTreeChain.chainTree.IsForest` (from `ShiftLoopChainInv.shift` and `chainTree_isForest`);
6. `model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E` (`chainTree_isSubgraph`);
7. `model'.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E` (`chainTree_isSubgraph`);
8. `Disjoint ((Finset.range cfg.P.d).biUnion (fun j => (activeLSF j).F.F.E)) (oldLastF.E ∪ newLastF.E)`
   (`initChain_prefix_disjoint` before and after the terminal shift);
9. `oldLastF.m + newLastF.m ≤ 2 * levelM cfg.TP cfg.P cfg.P.d` (each terminal LSF is a subgraph
   of `model.chain.G cfg.P.d`, whose edge count is bounded by `levelM cfg.TP cfg.P cfg.P.d`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain SparseCore.Program

/-- From `solverStateRep.rep` and `foot < heap < 2 ^ w`, the terminal branch count `lastK`
fits strictly below `2 ^ w`. -/
theorem lastK_lt_two_pow_of_rep {cfg : Alg2Config} {w L P m V psi k epsExp drainUnit root heap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < heap)
    (hheapW : heap < 2 ^ w) :
    model.chain.lastK < 2 ^ w := by
  have htermBound : tok.termHandle + 1 + model.chain.lastK ≤ tok.termTok :=
    hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  have htags := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hOwn := htags.1
  have hT19 := htags.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlt : tok.termTok - 1 < heap := by
    refine hbelow (tok.termTok - 1) (Or.inl (hOwn _ ?_))
    have hfoot19 : tok.termHandle ≤ tok.termTok - 1 ∧ tok.termTok - 1 < tok.termTok := by omega
    rw [hT19 _ hfoot19]
    decide
  omega

/-- Under `ChainInv` and `cfg.ValidOrdNoHidden`, each terminal-level LSF `lastLSFs j` (`j < lastK`)
has at most `levelM cfg.TP cfg.P cfg.P.d` edges, since it is a subgraph of `ch.G cfg.P.d`. -/
theorem lastLSF_m_le_levelM_d {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {ch : ChainState cfg.T cfg.P}
    (hInv : Chain.Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    {j : ℕ} (hj : j < ch.lastK) :
    (ch.lastLSFs j).F.F.m ≤ levelM cfg.TP cfg.P cfg.P.d := by
  have hB := Chain.Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hInv
  have hEsub : (ch.lastLSFs j).F.F.E ⊆ (ch.G cfg.P.d).E := (hInv.hLastHolds j hj).2.1.2.2.2.2.2.1
  have hGdM : (ch.G cfg.P.d).m ≤ levelM cfg.TP cfg.P cfg.P.d := by
    exact_mod_cast (hB cfg.P.d le_rfl).2.2.1
  exact le_trans (Finset.card_le_card hEsub) hGdM

/-- Proves preconditions (1), (2), (5), (6), (7), (8), and (9) of `ShiftTermChainSyncSpecWExt`
(at `lastTreeCap = 2 * levelM cfg.TP cfg.P cfg.P.d`) from `Chain.Ordered.ShiftLoopChainInv cfg
model.chain`, `solverStateRep.rep`, `hbelow`, and `heap < 2 ^ w`. Preconditions (3) and (4)
(`hlogW` and `hcapTree`) are already carried directly by `updateCycleLoop_ind_credit`. -/
theorem shiftTerm_reached_facts_1_to_9 {cfg : Alg2Config}
    {w L P m V psi k epsExp drainUnit root heap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hV : cfg.ValidOrdNoHidden)
    (hLoopInv : Chain.Ordered.ShiftLoopChainInv cfg model.chain)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < heap)
    (hheapW : heap < 2 ^ w) :
    let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
    let oldLastF := (model.chain.lastLSFs model.chain.lastBran).F.F
    let newLastF := (model.chain.lastLSFs ((model.chain.lastBran + 1) % model.chain.lastK)).F.F
    model.chain.lastBran < model.chain.lastK ∧
    model.chain.lastK < 2 ^ w ∧
    model'.chain.toTreeChain.chainTree.IsForest ∧
    model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E ∧
    model'.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E ∧
    Disjoint
      ((Finset.range cfg.P.d).biUnion fun j => (model.chain.toTreeChain.activeLSF j).F.F.E)
      (oldLastF.E ∪ newLastF.E) ∧
    oldLastF.m + newLastF.m ≤ 2 * levelM cfg.TP cfg.P cfg.P.d := by
  dsimp only
  set model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
  have hInv : Chain.Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ model.chain := hLoopInv.1
  have hLoopInv' : Chain.Ordered.ShiftLoopChainInv cfg model'.chain :=
    alg2LoopShiftStep_shiftLoopChainInv hV hLoopInv (Fin.last cfg.P.d)
  have hInv' : Chain.Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ model'.chain := hLoopInv'.1
  have hHolds := (hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hSub := model.chain.toTreeChain.forestsAreSubgraphs_of_holds hHolds
  have hHolds' := (hInv'.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hSub' := model'.chain.toTreeChain.forestsAreSubgraphs_of_holds hHolds'
  have hG0Eq : model'.chain.G 0 = model.chain.G 0 := by
    simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
  have hDisjOld : Disjoint
      ((Finset.range cfg.P.d).biUnion fun j => (model.chain.toTreeChain.activeLSF j).F.F.E)
      (model.chain.lastLSFs model.chain.lastBran).F.F.E := by
    have h := initChain_prefix_disjoint hHolds (le_refl cfg.P.d)
    simpa [TreeChain.activeLSF, ChainState.toTreeChain] using h
  have hDisjNew : Disjoint
      ((Finset.range cfg.P.d).biUnion fun j => (model.chain.toTreeChain.activeLSF j).F.F.E)
      (model.chain.lastLSFs ((model.chain.lastBran + 1) % model.chain.lastK)).F.F.E := by
    have h := initChain_prefix_disjoint hHolds' (le_refl cfg.P.d)
    have hPrefEq : (Finset.range cfg.P.d).biUnion (fun j => (model'.chain.toTreeChain.activeLSF j).F.F.E) =
        (Finset.range cfg.P.d).biUnion (fun j => (model.chain.toTreeChain.activeLSF j).F.F.E) := by
      refine Finset.biUnion_congr rfl fun j hj => ?_
      have hjd : j < cfg.P.d := Finset.mem_range.mp hj
      simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift, TreeChain.activeLSF,
        ChainState.toTreeChain, hjd]
    have hLastEq : model'.chain.toTreeChain.activeLSF cfg.P.d =
        model.chain.lastLSFs ((model.chain.lastBran + 1) % model.chain.lastK) := by
      simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift, TreeChain.activeLSF,
        ChainState.toTreeChain]
    change Disjoint
      ((Finset.range cfg.P.d).biUnion fun j => (model'.chain.toTreeChain.activeLSF j).F.F.E)
      (model'.chain.toTreeChain.activeLSF cfg.P.d).F.F.E at h
    rw [hPrefEq, hLastEq] at h
    exact h
  have hOldM : (model.chain.lastLSFs model.chain.lastBran).F.F.m ≤ levelM cfg.TP cfg.P cfg.P.d :=
    lastLSF_m_le_levelM_d hV hInv hInv.hLastBran
  have hNewM : (model.chain.lastLSFs ((model.chain.lastBran + 1) % model.chain.lastK)).F.F.m ≤
      levelM cfg.TP cfg.P cfg.P.d :=
    lastLSF_m_le_levelM_d hV hInv (Nat.mod_lt _ hInv.hLastK)
  refine ⟨hInv.hLastBran, lastK_lt_two_pow_of_rep hrep hbelow hheapW,
    model'.chain.toTreeChain.chainTree_isForest hHolds' hSub',
    (model.chain.toTreeChain.chainTree_isSubgraph hHolds hSub).2.1,
    hG0Eq ▸ (model'.chain.toTreeChain.chainTree_isSubgraph hHolds' hSub').2.1,
    Finset.disjoint_union_right.mpr ⟨hDisjOld, hDisjNew⟩,
    by omega⟩

end MinCostFlow.MinRatio
