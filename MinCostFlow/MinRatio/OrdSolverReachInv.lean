module

public import MinCostFlow.MinRatio.MinRatioMachineAssembly

/-!
# Invariants of the reachable solver states

`DSRep.Implements` asks each operation to work from every state that the representation holds
and that meets the contract's precondition. The contract `minRatioMachineContractWithV` has no
history in its precondition, so a fact that holds only for states reached from `Init` must be
part of the representation. This file adds such facts to `solverStateRep`.

The wrapper `solverStateRepInv` has the footprint and the potential of `solverStateRep` and adds
`OrdSolverReachInv`. That invariant has two parts.
- `OrdSolverReachBase` is about the model alone: the live graph is the fixed graph `G` (every
  batch is a refresh batch), and lengths are positive.
- `SolverTreeNumericInv` is the numeric budget of the path tree that `Detect` needs.

The name facts that involve the token (`0 < tok.intCap`, `model.nextFresh ≤ tok.intCap`, and
that names at or above `tok.intCap` map to themselves) are part of `solverStateRep` itself, since the sub-procedures that change the token are given by
specifications that return a new token with no relation to the old one, except through
`solverStateRep`.

We prove that `Init` makes the base part true (`ordSolverReachBase_init`) and that `Update` and
`Detect` keep it (`ordSolverReachBase_update`, `ordSolverReachBase_detect`). `Query` does not
change the model. The numeric part is handled in `MinRatio/OrdSolverImplements.lean`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore.Program

/-- The model facts kept by every reachable state of ordered Algorithm 2 on the fixed graph
`G`: the live external graph is `G`, every live edge has a positive length, and every active
branch index is strictly below `cfg.P.k` (`BranchesLtK`). -/
@[expose] def OrdSolverReachBase {cfg : Alg2Config} (G : MGraph) (model : Alg2State cfg) :
    Prop :=
  model.extG = G ∧ (∀ e ∈ model.extG.E, 0 < model.extℓ e) ∧ BranchesLtK cfg model

/-- The invariant of the reachable solver states: the model facts `OrdSolverReachBase` and the
numeric budget `SolverTreeNumericInv` of the path tree. -/
@[expose] def OrdSolverReachInv {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (G : MGraph) (P : ℕ)
    (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) : Prop :=
  OrdSolverReachBase G model ∧ SolverTreeNumericInv P model tok

/-- `solverStateRep` together with the reachable-state invariant `OrdSolverReachInv`. The
footprint and the potential are those of `solverStateRep`. -/
@[expose] noncomputable def solverStateRepInv (cfg : Alg2Config) (G : MGraph)
    (L P m V psi k epsExp drainUnit : ℕ) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) :
    DSRep (Alg2State cfg) where
  τ := SolverToken cfg L Rcore
  rep root model tok mem :=
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem ∧
    OrdSolverReachInv G P model tok
  foot := (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot
  phi := (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi

/-- `solverStateRepInv` is local, since `OrdSolverReachInv` does not read memory and
`solverStateRep` is local (`solverStateRep_local`). -/
theorem solverStateRepInv_local (cfg : Alg2Config) (G : MGraph)
    (L P m V psi k epsExp drainUnit : ℕ) {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (hlocalCore : Rcore.Local) :
    (solverStateRepInv cfg G L P m V psi k epsExp drainUnit Rcore).Local := by
  intro b s x mem mem' hag
  obtain ⟨hrep, hphi⟩ :=
    solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocalCore b s x mem mem' hag
  exact ⟨fun h => ⟨hrep h.1, h.2⟩, hphi⟩

/-- The name-table facts that `solverStateRep` records: the tables are not empty, and they have
room for every name handed out so far. -/
theorem solverStateRep_intCap {cfg : Alg2Config} {L P m V psi k epsExp drainUnit root : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem) :
    0 < tok.intCap ∧ model.nextFresh ≤ tok.intCap ∧ ∀ j ≥ tok.intCap, model.intToExt j = j := by
  obtain ⟨_, _, _, _, _, _, _, hcap, _⟩ := hrep
  exact hcap.2

/-- The path tree of a represented state has one vertex per vertex of the live graph. -/
theorem solverStateRep_tree_n {cfg : Alg2Config} {L P m V psi k epsExp drainUnit root : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem) :
    tok.tree.n = model.extG.n := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, htn, _⟩ := hrep
  exact htn

/-- The path tree of a represented state meets the link-cut invariant. -/
theorem solverStateRep_lctInv {cfg : Alg2Config} {L P m V psi k epsExp drainUnit root : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem) :
    LctInvWith pathPayload tok.tree tok.trees tok.free tok.depth := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlct, _⟩ := hrep
  exact hlct

/-- The numeric budget gives the two fits of the path tree that `Query` needs: the tree fits
in `L` limbs, and so does the tree after exposing any active node. Both follow from
`PathTreeNumericInv.fits` and `pathTreeFits_expose_of_numeric`, with the capacity premise of
`SolverTreeNumericInv`. -/
theorem SolverTreeNumericInv.fits {cfg : Alg2Config} {L P m V psi k epsExp drainUnit root : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hnum : SolverTreeNumericInv P model tok) :
    pathTreeFits 4 L tok.tree ∧
      ∀ slot, pathTreeActive tok.tree slot →
        pathTreeFits 4 L (lctExpose pathPayload tok.tree slot) := by
  obtain ⟨B, R, hn, hcap, _, _⟩ := hnum
  have W := solverStateRep_lctInv hrep
  exact ⟨hn.fits W hcap, fun _ hx => pathTreeFits_expose_of_numeric W hn hcap hx⟩

/-- `Init` makes the model facts true: `algorithm2_init` keeps `G` as the live graph, starts
the counter at `G.E.sup id + 1`, uses the identity for names, and takes the given lengths,
which are positive by hypothesis. -/
theorem ordSolverReachBase_init (cfg : Alg2Config) (G : MGraph) (g l : ℕ → ℝ)
    (hl : ∀ e ∈ G.E, 0 < l e) :
    OrdSolverReachBase G (Chain.Ordered.algorithm2_init cfg G g l) :=
  ⟨rfl, hl, branchesLtK_init cfg G g l⟩

/-- Translating a batch updates the external graph by the batch itself. -/
theorem translateBatch_fst (U : List Update) :
    ∀ (G : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ),
      (translateBatch G e2i i2e nf U).1 = G.applyBatch U := by
  induction U with
  | nil => intro _ _ _ _; rfl
  | cons u us ih =>
    intro G e2i i2e nf
    cases u with
    | insert _ _ _ => exact ih _ _ _ _
    | delete _ => exact ih _ _ _ _
    | split _ _ _ _ => exact ih _ _ _ _

/-- The fields of the model that `Update` takes from the batch translation and the new
lengths. Both outcomes of the cycle loop (with or without a good cycle) set them in the same
way. -/
theorem algorithm2_update_names (cfg : Alg2Config) (κ : ℝ) (model : Alg2State cfg)
    (U : List Update) (g l : ℕ → ℝ) (η : ℝ) :
    let r := ((Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).update model U g l η).1
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    r.extG = tr.1 ∧ r.extℓ = l := by
  dsimp only
  change ((Chain.Ordered.algorithm2_updateWith cfg κ model U g l η).1).extG = _ ∧
    ((Chain.Ordered.algorithm2_updateWith cfg κ model U g l η).1).extℓ = _
  unfold Chain.Ordered.algorithm2_updateWith
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

/-- `Update` keeps the model facts. The live graph stays `G`, since a refresh batch has
`G.applyBatch U = G` (`RefreshBatch`). The new lengths are the given ones, positive on `G` by
hypothesis. -/
theorem ordSolverReachBase_update {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {model : Alg2State cfg} {U : List Update} {g l : ℕ → ℝ} {η : ℝ}
    (hbase : OrdSolverReachBase G model) (hU : RefreshBatch G U) (hl : ∀ e ∈ G.E, 0 < l e) :
    OrdSolverReachBase G
      ((Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).update model U g l η).1 := by
  obtain ⟨hG, _, hBr⟩ := hbase
  obtain ⟨hE', hl'⟩ := algorithm2_update_names cfg κ model U g l η
  have hextG : ((Chain.Ordered.algorithm2_dsWithFailureWith cfg κ).update model U g l η).1.extG =
      G := by
    rw [hE', translateBatch_fst, hG, hU.2.1]
  refine ⟨hextG, ?_, branchesLtK_update hBr⟩
  rw [hextG, hl']
  exact hl

/-- `Detect` keeps the model facts, since it changes only the detector accounts and the
operation counter (`algorithm2_detect`). -/
theorem ordSolverReachBase_detect {cfg : Alg2Config} {G : MGraph} {model : Alg2State cfg}
    (hbase : OrdSolverReachBase G model) :
    OrdSolverReachBase G (algorithm2_detect cfg model).2 :=
  ⟨hbase.1, hbase.2.1, branchesLtK_detect hbase.2.2⟩

end MinCostFlow.MinRatio

end
