module

public import MinCostFlow.Scaling.ShortestRoutingModel
public import MinCostFlow.Scaling.SolverContract

/-!
# Edge blocks in the shortest-routing graph layout

The shortest-routing graph keeps every original edge slot, replacing each
positive capacity by `n+1` and leaving zero capacities zero. The added
source contributes one zero-cost edge to every original vertex. These
identities connect both blocks to the shared five-word circulation layout.
-/

public section
namespace MinCostFlow.Scaling.Machine

/-- The old routing slots retain endpoints and costs, with capacity `n+1`
precisely when the original capacity is positive. -/
theorem shortestRouting_old_edgeWords (J : Circulation) (e : Fin J.m) :
    J.shortestRoutingGraph.solverEdgeWords (Fin.castAdd J.n e) =
      [(J.tail e).val, (J.head e).val, if 0 < J.capacity e then J.n+1 else 0,
        if J.cost e < 0 then 1 else 0, (J.cost e).natAbs] := by
  simp only [Circulation.solverEdgeWords, Circulation.shortestRoutingGraph,
    Fin.addCases_left, Fin.val_castSucc]

/-- Each added edge goes from the new source `n` to its old vertex, has
capacity `n+1`, and has zero cost. -/
theorem shortestRouting_source_edgeWords (J : Circulation) (v : Fin J.n) :
    J.shortestRoutingGraph.solverEdgeWords (Fin.natAdd J.m v) =
      [J.n, v.val, J.n+1, 0, 0] := by
  simp only [Circulation.solverEdgeWords, Circulation.shortestRoutingGraph,
    Fin.addCases_right, Fin.val_last, Fin.val_castSucc, lt_self_iff_false,
    ↓reduceIte, Int.natAbs_zero]

/-- The complete routing encoding consists of its header, original slots,
and then the added source slots, in the order used by the model. -/
theorem shortestRouting_solverWords (J : Circulation) :
    J.shortestRoutingGraph.solverWords = (J.n+1) :: (J.m+J.n) ::
      ((List.ofFn (fun e => J.shortestRoutingGraph.solverEdgeWords (Fin.castAdd J.n e))).flatten ++
        (List.ofFn (fun (v : Fin J.n) => [J.n,v.val,J.n+1,0,0])).flatten) := by
  unfold Circulation.solverWords
  rw [List.flatMap, ← List.ofFn_eq_map, List.ofFn_add, List.flatten_append]
  congr 1
  congr 1
  congr 1
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  exact shortestRouting_source_edgeWords J v

/-- The routing encoding in the exact list form produced by both scans. -/
theorem shortestRouting_solverWords_flatMap (J : Circulation) :
    J.shortestRoutingGraph.solverWords = [J.n+1,J.m+J.n] ++
      ((List.finRange J.m).flatMap (fun e => J.shortestRoutingGraph.solverEdgeWords (Fin.castAdd J.n e)) ++
       (List.finRange J.n).flatMap (fun v => J.shortestRoutingGraph.solverEdgeWords (Fin.natAdd J.m v))) := by
  rw [shortestRouting_solverWords]
  simp only [List.flatMap, ← List.ofFn_eq_map]
  simp_rw [shortestRouting_source_edgeWords]
  rfl

/-- All routing words fit whenever the original words and the two new
header values fit. This also covers every changed capacity and source arc. -/
theorem shortestRouting_words_fit (J : Circulation) (w : ℕ)
    (hinput : ∀ x ∈ J.solverWords, x < 2^w)
    (hn : J.n+1 < 2^w) (hm : J.m+J.n < 2^w) :
    ∀ x ∈ J.shortestRoutingGraph.solverWords, x < 2^w := by
  intro x hx
  change x ∈ (J.n+1) :: (J.m+J.n) :: _ at hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hn
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hm
  obtain ⟨e,_,he⟩ := List.mem_flatMap.mp hx
  revert he
  refine Fin.addCases (fun e => ?_) (fun v => ?_) e
  · intro he
    rw [shortestRouting_old_edgeWords] at he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
    · exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
    · split <;> omega
    · exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
    · exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
  · intro he
    rw [shortestRouting_source_edgeWords] at he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    have hv := v.isLt
    rcases he with rfl | rfl | rfl | rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
