module

public import MinCostFlow.HierPaths.BuildProgConnErase
import MinCostFlow.HierPaths.InitLayout
import MinCostFlow.HierPaths.QueryProgRoute

/-!
# Sizes of one routed connector block

The raw reply contains both endpoints and all the raw walks. It is
large enough to hold the compact result. Erasing loops does not increase
the number of edge words.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The cursor reserves one header and one slot for each raw edge. -/
theorem connectorWalkRow_cursor_size (M : List (ℕ × ℕ)) (emb : ℕ → List ℕ) (base i : ℕ) :
    (connectorWalkRow M emb).cursor base i = base+i+((List.range i).map fun j => (emb j).length).sum := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [BuildWalkRow.cursor,ih,sum_range_map_succ]
    simp [BuildWalkRow.raw,connectorWalkRow]
    omega

/-- The full reply has one tag, two child offsets, the endpoint pairs,
and the offsets and raw words of the walks. -/
theorem connectorReplyLength (M : List (ℕ × ℕ)) (emb : ℕ → List ℕ) :
    (routeResultWords (.matched [M] emb)).length =
      8+3*M.length+((List.range M.length).map fun j => (emb j).length).sum := by
  change (layoutList [[0],csrList 1 (matchingRowWords [M]),csrList ([M] : List (List (ℕ × ℕ))).flatten.length emb]).length = _
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
  rw [length_layoutList]
  simp [List.range_succ,csrList,length_csrData_eq,length_matchingRowWords]
  omega

/-- The size of the connector CSR block is at most that of its raw reply. -/
theorem connectorRows_length_le {G : Graph} {M : List (ℕ × ℕ)} {emb : ℕ → List ℕ}
    (hWalk : ∀ i < M.length, IsEdgeWalk G.edges (edgeAt M i).1 (edgeAt M i).2 (emb i)) :
    (csrList M.length (buildConnectorRowWords (edgeAt M)
      (fun i => erase G.edges (edgeAt M i).1 (emb i)))).length ≤
      (routeResultWords (.matched [M] emb)).length := by
  let f := fun i => (buildConnectorRowWords (edgeAt M) (fun j => erase G.edges (edgeAt M j).1 (emb j)) i).length
  have hsum : ∀ i ≤ M.length, ((List.range i).map f).sum ≤
      2*i+((List.range i).map fun j => (emb j).length).sum := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      have hp := ih (by omega)
      have hm := ((erase_spec (emb i).length _ _ _ le_rfl
        (hWalk i (by omega))).2.1).length_le
      have hf : f i ≤ 2+(emb i).length := by simp [f,buildConnectorRowWords]; omega
      rw [sum_range_map_succ,sum_range_map_succ]
      omega
  have hh := hsum M.length le_rfl
  rw [connectorReplyLength,csrList,List.length_append,length_csrOffsets,length_csrData_eq]
  change M.length+1+((List.range M.length).map f).sum ≤ _
  omega

end MinCostFlow.HierPaths
