module

public import MinCostFlow.SparseCore.Program.RestartModelState
public import MinCostFlow.SparseCore.Program.AssemblyModel

/-!
# The model facts that a branch of the sparse-core program needs (`AssemblyBranchFacts`)

A branch of the sparse-core program (`AsmBranchAt`, `AssemblyTopIface.lean`) holds one state
`tr : BundleTreeState depth` of the bundle tool and the input order `ord`. Its operations call
pieces whose preconditions are facts about this state: the LSF meets its invariant, the output
graph `S_cur` has the shape that the restart rebuilds, distinct bundles share no edge, and so on.

The model proves such facts along whole runs, not for one step from an invariant. So the branch
does not keep them in its representation. Its operations take them as one hypothesis on the
model state, and the top layer proves that hypothesis from the run invariants of the model. This
file states that hypothesis, `AsmBrModelFacts`. It imports only model files, so that the top layer
can state it in `AsmBranchAt`.

The facts are about the model state alone, except the caps `vCap` and `eCap` of the instance, which
bound the names of the vertices and the edges.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-- The bundles of distinct active pairs have no common edge, and no bundle edge of an active
pair is a cross edge of the LSF state. -/
def BunDisjointInv {L : ℕ} (tr : BundleTreeState L) : Prop :=
  (∀ p₁ ∈ activePairs tr, ∀ p₂ ∈ activePairs tr, p₁ ≠ p₂ →
    Disjoint (tr.bun p₁).edges (tr.bun p₂).edges) ∧
  ∀ p ∈ activePairs tr, Disjoint (tr.bun p).edges tr.cs.crossEdges

/-- **The model facts of one branch state** `tr` with input order `ord`, for the sparsifier
`impl` and the caps `vCap`, `eCap` of the instance:
1. the branch has at least one tree (`1 ≤ k`);
2. the LSF state meets `CompLSFInv`, and `ord` is the order of a rotation of its graph;
3. `RestartScurModelInv`: the active components are components of `G₀`, the output graph `S_cur`
   lies on the roots and has the edges of the spanners, the extra edges and the cross edges, the
   core graph is a subgraph of `S_cur`, and the bundles and spanners of the active pairs sit in
   the core graph;
4. `BunDisjointInv`: distinct active bundles share no edge, and no bundle edge is a cross edge;
5. `S_cur` is a valid graph;
6. the spanner parameters of the state absorb those of `canonicalSparsify impl` at `m₀`, and the
   spanner constant is at least `dsAmortConst impl`;
7. the names of the vertices of the graph are below `vCap`, and the names of its edges and of the
   edges of `S_cur` are below `eCap`. -/
def AsmBrModelFacts {depth : ℕ} (impl : SparsifyImpl) (vCap eCap : ℕ)
    (tr : BundleTreeState depth) (ord : ℕ → List End) : Prop :=
  1 ≤ tr.k ∧
  (∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (_ : CompLSFInv C_lsst ℓ₀ tr.cs) (ρ : Rotation tr.cs.G),
    ρ.order = ord) ∧
  RestartScurModelInv tr ∧
  BunDisjointInv tr ∧
  tr.S_cur.IsValid ∧
  SparsifyParamsLe (canonicalSparsifyParams impl tr.m₀).absorbTime tr.spanParams ∧
  dsAmortConst impl ≤ tr.spanConst ∧
  (∀ x ∈ tr.cs.G.V, x < vCap) ∧ (∀ e ∈ tr.cs.G.E, e < eCap) ∧ (∀ e ∈ tr.S_cur.E, e < eCap)

end MinCostFlow.SparseCore.Program
