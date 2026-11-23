module

public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
public import MinCostFlow.MinRatio.OrdSolverReachInv

/-!
# From the select-aware core spec to the chain-update core spec (`WireChainCoreSelAdapt`)

The select-aware spec `OrdChainUpdateCoreSpecWKFBLSel` (`OrdSelSpecs.lean`) and the chain-update
core spec `OrdChainUpdateCoreSpecWExtKFBL` (`WireChainCoreSpecKFBL.lean`) state the facts at the
start of `Update` in different forms. This file proves the parts of the second form that follow
from the first one at once:
* `updateCore_treeFit_of_solverTreeNumericInv`: `SolverTreeNumericInv` gives bounds `B`, `R` with
  `PathTreeNumericInv` and the capacity fit at `model.extG.n`, since the path tree has one vertex
  per live vertex.
* `updateCore_vecOffFoot_of_not_foot`: the footprint part of `UpdateCoreModelInv` (the words of the
  vectors `g` and `l` lie off the owned cells, the tree and every level core) is the statement
  that these words lie off the footprint of `solverStateRep`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain SparseCore.Program

/-- `SolverTreeNumericInv` gives the tree bounds and the capacity fit that the chain-update core
takes, at the vertex count of the live graph. -/
theorem updateCore_treeFit_of_solverTreeNumericInv {cfg : Alg2Config}
    {L P m V psi k epsExp drainUnit root : ℕ} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hNum : SolverTreeNumericInv P model tok) :
    ∃ B R : ℤ, PathTreeNumericInv tok.tree tok.trees B R ∧
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) := by
  obtain ⟨B, R, hT, hFit, _, _⟩ := hNum
  exact ⟨B, R, hT, by rw [← solverStateRep_tree_n hrep]; exact hFit⟩

/-- Words off the footprint of `solverStateRep` are off the owned cells, the tree and every level
core: this is the footprint part of `UpdateCoreModelInv` for the vectors `g` and `l`. -/
theorem updateCore_vecOffFoot_of_not_foot {cfg : Alg2Config}
    {L P m V psi k epsExp drainUnit root g l : ℕ} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {tok : SolverToken cfg L Rcore}
    (hg : ∀ j < m * L,
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok (g + j))
    (hl : ∀ j < m * L,
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok (l + j)) :
    (∀ j < m * L, ¬ tok.owned (g + j) ∧
      ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok (g + j) ∧
      ∀ r < cfg.P.d, ¬ Rcore.foot (tok.coreHandle r) (tok.coreTok r) (g + j)) ∧
    (∀ j < m * L, ¬ tok.owned (l + j) ∧
      ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok (l + j) ∧
      ∀ r < cfg.P.d, ¬ Rcore.foot (tok.coreHandle r) (tok.coreTok r) (l + j)) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have h := hg j hj
    simp only [solverStateRep, not_or, not_exists, not_and] at h
    exact ⟨h.1, h.2.1, fun r hr => h.2.2 r hr⟩
  · have h := hl j hj
    simp only [solverStateRep, not_or, not_exists, not_and] at h
    exact ⟨h.1, h.2.1, fun r hr => h.2.2 r hr⟩

end MinCostFlow.MinRatio
