module

public import MinCostFlow.Scaling.ReductionAlgorithm
public import MinCostFlow.Scaling.IsolatedDemands
public import MinCostFlow.Scaling.VertexCompression
import MinCostFlow.Scaling.VertexCompressionSize

/-!
# Uniform solver dimensions for the outer reduction

After the isolated-demand check, the compacted feasibility circulation
has at most `3*m` edges. A residual circulation has at most `2*m` edges
before compaction. Both retain at most one extra original vertex before
compression. The complete nested scaling budgets therefore compare with
`T(8*n,72*m)` whenever the compacted graph is nonempty. Empty compacted
graphs make no primitive solver call and need no such comparison.
-/

public section
namespace MinCostFlow.Scaling.Machine

private theorem instance_vertices_pos (I : Instance) (hv : I.IsValid) (hm : 0<I.m) : 0<I.n :=
  (Nat.zero_le _).trans_lt ((FlowReduction.shiftedGraph I hv).tail ⟨0,hm⟩).isLt

private theorem comparison_dimensions (I : Instance) (hv : I.IsValid) (J : Circulation)
    (hn : J.n≤I.n+1) (hm : J.m≤3*I.m) (hpos : 0<J.m) :
    J.compress.n+3≤8*I.n ∧ 16*J.m+4*J.compress.n≤72*I.m := by
  have hvn := J.compress_vertices_le
  have he := J.endpointLabels_count_le
  change J.compress.n≤2*J.m at he
  have hIm : 0<I.m := by omega
  have hIn := instance_vertices_pos I hv hIm
  exact ⟨by omega,by omega⟩

/-- The actual compacted feasibility graph fits the original uniform
solver dimensions after the algorithm's isolated-demand check. -/
theorem feasibility_compacted_solver_dimensions (I : Instance) (hv : I.IsValid)
    (hiso : FlowReduction.isolatedCheck I hv=true) :
    let K := (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
    0<K.m → K.compress.n+3≤8*I.n ∧ 16*K.m+4*K.compress.n≤72*I.m := by
  intro K hk
  apply comparison_dimensions I hv K (by change I.n+1≤I.n+1; exact le_rfl) ?_ hk
  change (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges.m≤3*I.m
  rw [FlowReduction.buildFeasibilityInstance_eq]
  exact FlowReduction.feasibilityInstance_positiveEdges_le_three I hv hiso

/-- Every actual compacted residual graph fits the same original uniform
solver dimensions, independently of the starting flow's coordinates. -/
theorem residual_compacted_solver_dimensions (I : Instance) (hv : I.IsValid) (f : Fin I.m → ℤ) :
    let K := ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
    0<K.m → K.compress.n+3≤8*I.n ∧ 16*K.m+4*K.compress.n≤72*I.m := by
  intro K hk
  have he := ((FlowReduction.shiftedGraph I hv).residual f).positiveEdges_length_le
  change K.m≤I.m+I.m at he
  exact comparison_dimensions I hv K (by change I.n≤I.n+1; omega) (by omega) hk

end MinCostFlow.Scaling.Machine
