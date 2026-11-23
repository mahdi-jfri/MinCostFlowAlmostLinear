module

public import MinCostFlow.Statement.Cited.AbrahamNeiman
public import MinCostFlow.Statement.Cited.ChuzhoyEtAl
public import MinCostFlow.Statement.Cited.ChuzhoySaranurak

/-!
# Checks of the cited statements on small examples

These examples test the graph notions of `MinCostFlow/Statement/Cited/` on small graphs: degrees,
volumes and cuts, induced subgraphs, paths, the encoding and its reading back from memory.
-/

namespace MinCostFlow.Cited

/-- A path on three vertices, `0 - 1 - 2`. -/
def path3 : Graph :=
  ⟨3, [(0, 1), (1, 2)]⟩

/-- Degrees: the middle vertex has degree 2, the ends degree 1; the volume of all vertices is
`2m = 4`. -/
example : path3.deg 0 = 1 ∧ path3.deg 1 = 2 ∧ path3.deg 2 = 1 ∧ path3.vol path3.verts = 4 := by
  decide

/-- The cut of `{0}` has one edge, the cut of `{1}` has two. -/
example : path3.cut {0} = 1 ∧ path3.cut {1} = 2 := by
  decide

/-- In `G[{0, 1}]` only the edge `0 - 1` remains: the degree of `1` is `1` there. -/
example : path3.degIn {0, 1} 1 = 1 ∧ path3.cutIn {0, 1} {0} = 1 := by
  decide

/-- Two parallel edges are a loopless multigraph, but not a simple graph. -/
example : (⟨2, [(0, 1), (1, 0)]⟩ : Graph).IsLoopless ∧ ¬ (⟨2, [(0, 1), (1, 0)]⟩ : Graph).IsSimple := by
  refine ⟨by unfold Graph.IsLoopless; decide, fun ⟨_, h⟩ => ?_⟩
  simp at h

/-- `[0, 1, 2]` is a path from `0` to `2` along the edges of `path3`. -/
example : IsPathAlong path3.edges 0 2 [0, 1, 2] := by
  unfold IsPathAlong
  decide

/-- Reading a graph back from memory that holds its encoding gives the graph. -/
example : readGraph (fun i => path3.encode.getD i 0) 0 = path3 :=
  rfl

end MinCostFlow.Cited
