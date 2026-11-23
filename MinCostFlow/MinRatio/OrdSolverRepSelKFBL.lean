module

public import MinCostFlow.MinRatio.OrdSelSpecs
public import MinCostFlow.MinRatio.SolverSelectPreserve
public import MinCostFlow.MinRatio.SolverSelectRegionInv
public import MinCostFlow.MinRatio.SolverTreeBudgetInv
import Mathlib.Tactic

/-!
# Select-aware `KFBL` solver representation (`OrdSolverRepSelKFBL`)

Wraps `solverStateRepSel` (`SolverSelectState.lean`) with the three invariants required by the
`KFBL` select-aware solver operations without modifying `SolverSelectState.lean`:
* `SolverLevelCapsInv P V G.n (initTargetCap cfg G) model tok.1.1.1 mem`,
* `DeepInv model.chain` (instantiated by `DryChainLenGridInv J` in the dry run), and
* `SolverSelectRegionInv` (`SolverSelectRegionInv.lean`) at the caps `(G.n, initTargetCap cfg G)`,
  the gradient exponent `E`, the terminal precision `pLast` and the slot size `slot`: the owned
  blocks layout, the potential bound and the gradient bound that every rebuild of a level needs,
  and
* `SolverTreeBudgetInv` (`SolverTreeBudgetInv.lean`) with the raise
  `X = maxPaths · 2^(3E + 2 + P)` of one good cycle: the tree budget
  `B₀ + updateCount · X`, `updateCount · X` that holds between operations.

`solverStateRepSelKFBL` keeps the exact same witness type `τ`, footprint `foot`, and potential
`phi` (`solverStateRepFull.phi + K * tok.2.reembPot`) as `solverStateRepSel`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore.Program

/-- **The `KFBL` select-heap solver representation:** wraps `solverStateRepSel` with
`SolverLevelCapsInv P V G.n (initTargetCap cfg G)`, `DeepInv model.chain`,
`SolverSelectRegionInv` and `SolverTreeBudgetInv`, preserving `τ`, `foot`, and `phi`
identically. -/
@[expose] noncomputable def solverStateRepSelKFBL (cfg : Alg2Config) (κ : ℝ) (G : MGraph)
    (L P m V psi k epsExp drainUnit unit toolMul treeMul dMul kOff E pLast slot maxPaths : ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (K : ℕ) (pot : cfg.T.State → ℕ)
    (DeepInv : ChainState cfg.T cfg.P → Prop) :
    DSRep (Alg2State cfg) where
  τ := (solverStateRepSel cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul dMul kOff
    Rcore K pot).τ
  rep root model tok mem :=
    (solverStateRepSel cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul dMul kOff
      Rcore K pot).rep root model tok mem ∧
    SolverLevelCapsInv P V G.n (initTargetCap cfg G) model tok.1.1.1 mem ∧
    SolverLevelLayoutAt G.n (initTargetCap cfg G) tok.1.1.1 mem ∧
    DeepInv model.chain ∧
    SolverSelectRegionInv G L P m E pLast slot G.n (initTargetCap cfg G) model
      ((solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).foot
        root tok.1) tok.1.1.1 tok.2 mem ∧
    SolverTreeBudgetInv G P E ((maxPaths : ℤ) * 2 ^ (3 * E + 2 + P)) model tok.1.1.1 mem
  foot root tok :=
    (solverStateRepSel cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul dMul kOff
      Rcore K pot).foot root tok
  phi root tok mem :=
    (solverStateRepSel cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul dMul kOff
      Rcore K pot).phi root tok mem

/-- `solverStateRepSelKFBL` is local: `solverStateRepSel` is local, `LevelMetaFoot` lies inside
the solver's foot (`LevelMetaFoot.mem_foot`), `DeepInv` does not read memory, and
`SolverSelectRegionInv` reads only the level metadata and the owned cells, which both lie in the
foot (`SolverSelectRegionInv.congr`), and `SolverTreeBudgetInv` reads only the record pointers,
which have tag `13` (`solverStateRep_recPtr_foot`). -/
theorem solverStateRepSelKFBL_local (cfg : Alg2Config) (κ : ℝ) (G : MGraph)
    (L P m V psi k epsExp drainUnit unit toolMul treeMul dMul kOff E pLast slot maxPaths : ℕ)
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    (K : ℕ) (pot : cfg.T.State → ℕ) (DeepInv : ChainState cfg.T cfg.P → Prop) :
    (solverStateRepSelKFBL cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul dMul kOff
      E pLast slot maxPaths Rcore K pot DeepInv).Local := by
  intro root model tok mem₁ mem₂ hag
  obtain ⟨hrepSel, hphiSel⟩ := solverStateRepSel_local cfg κ G L P m V psi k epsExp drainUnit
    unit toolMul treeMul dMul kOff hlocalCore K pot root model tok mem₁ mem₂ hag
  refine ⟨fun ⟨hSel, hCaps, hLay, hDeep, hReg, hBud⟩ => ?_, hphiSel⟩
  have hPres : PreservesLevelMeta tok.1.1.1 tok.1.1.1 mem₁ mem₂ :=
    (PreservesLevelMeta.refl tok.1.1.1 mem₁).congr_mem_right fun a ht =>
      (hag a (Or.inl (LevelMetaFoot.mem_foot hSel.1.1.1 ht))).symm
  refine ⟨hrepSel hSel, hPres.to_capsInv hCaps rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) rfl, hPres.to_levelLayout hCaps.1 hLay, hDeep, ?_⟩
  refine ⟨hReg.congr hCaps.1 hPres hReg.owned_not_foot (fun a ho => (hag a (Or.inr ho)).symm)
    rfl rfl rfl, ?_⟩
  exact hBud.of_agree fun e he =>
    (hag _ (Or.inl (solverStateRep_recPtr_foot hSel.1.1.1 he))).symm

/-- The potential of `solverStateRepSelKFBL` is `solverStateRepFull.phi + K * tok.2.reembPot`. -/
theorem solverStateRepSelKFBL_phi_eq {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {L P m V psi k epsExp drainUnit unit toolMul treeMul dMul kOff E pLast slot maxPaths K : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {pot : cfg.T.State → ℕ}
    {DeepInv : ChainState cfg.T cfg.P → Prop}
    {root : ℕ} {model : Alg2State cfg}
    {tok : ((SolverToken cfg L Rcore × ℕ) × (ℕ × ℕ)) × SelectGhost} {mem : ℕ → ℕ}
    (hrep : (solverStateRepShift cfg L P m V psi k epsExp drainUnit unit Rcore).rep root model
      tok.1.1 mem)
    (hrc : tok.1.2.1 = runtimeCredit cfg model)
    (htc : tok.1.2.2 = treeCredit cfg model) :
    (solverStateRepSelKFBL cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul dMul kOff
      E pLast slot maxPaths Rcore K pot DeepInv).phi root tok mem =
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok.1.1.1 mem +
        K * tok.2.reembPot +
        unit * (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain +
          chainShiftDeposit cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain) +
        unit * fwdPotential cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) model.chain +
        toolMul * runtimeCredit cfg model + treeMul * treeCredit cfg model := by
  dsimp only [solverStateRepSelKFBL, solverStateRepSel]
  rw [solverStateRepFull_phi_eq (κ := κ) (G := G) hrep hrc htc]
  omega

end MinCostFlow.MinRatio
