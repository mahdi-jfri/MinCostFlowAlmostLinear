module

public import MinCostFlow.Scaling.AdjacencyLayout
public import MinCostFlow.Scaling.WordPairStoreProgram

/-!
# Clearing a stored adjacency head

When label propagation loads a newly reached vertex's outgoing edges, it
clears that vertex's adjacency list. The existing pair writer stores a
null pointer and zero length. Its exact frame preserves every node, so the
loaded list remains available for copying into the pending list. The cost
is 14 and no fresh memory is allocated.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The writer receives `[0,0,headCell]`. The node range follows the whole
vertex table, so changing the head cannot modify a stored list node. -/
def adjacencyClearContract (w heads lo bound : ℕ) {n m : ℕ}
    (out : Fin n → List (Fin m)) (v : Fin n) : Contract where
  pre args mem := args = [0, 0, heads+2*v.val] ∧ AdjacencyAt mem heads lo bound out ∧
    heads+2*n ≤ lo ∧ heads+2*n < 2 ^ w
  post _ mem ret mem' := ret = heads+2*v.val+2 ∧
    AdjacencyAt mem' heads lo bound (Function.update out v []) ∧
    ∀ x, x < heads+2*v.val ∨ heads+2*v.val+2 ≤ x → mem' x = mem x
  cost _ _ := 14

/-- The shared pair writer clears exactly one vertex's outgoing list while
preserving all list nodes and every other old cell. -/
theorem adjacencyClear_meetsContract {w b heads lo bound n m : ℕ} {p : Program}
    (hp : p.HasAt b wordPairModule) (out : Fin n → List (Fin m)) (v : Fin n) :
    MeetsContract w p b (adjacencyClearContract w heads lo bound out v) := by
  intro args mem pos ω hwords hpre
  obtain ⟨rfl, hat, hheadsEnd, hspace⟩ := hpre
  have hv := v.isLt
  have hcellEnd : heads+2*v.val+2 ≤ heads+2*n := by omega
  have hcellSpace : heads+2*v.val+2 < 2 ^ w := hcellEnd.trans_lt hspace
  obtain ⟨body, hbody, o, st, cost, hrun, hpost, hcost⟩ :=
    wordPairStore_meetsContract hp [0, 0, heads+2*v.val] mem pos ω hwords
      ⟨0, 0, heads+2*v.val, rfl, hcellSpace⟩
  obtain ⟨hret, hstored, hframe⟩ := hpost
  change o.value = heads+2*v.val+2 at hret
  change ListAt st.mem (heads+2*v.val) [0, 0] at hstored
  change (∀ x, x < heads+2*v.val ∨ heads+2*v.val+2 ≤ x → st.mem x = mem x) at hframe
  have htable : AdjacencyAt st.mem heads lo bound (Function.update out v []) := by
    refine hat.update v [] 0 hheadsEnd le_rfl hstored .nil ?_ ?_
    · intro x hx _
      exact hframe x (Or.inr (by omega))
    · intro x _ hx0 hx1
      apply hframe
      omega
  exact ⟨body, hbody, o, st, cost, hrun, ⟨hret, htable, hframe⟩, hcost⟩

/-- Empty initialization realizes all clear-head premises for every valid
vertex, with a separate immutable-node range. -/
theorem exists_adjacencyClear_pre {n m : ℕ} (v : Fin n) :
    ∃ w lo, (∀ x ∈ [0, 0, 2*v.val], x < 2 ^ w) ∧
      (adjacencyClearContract w 0 lo lo (fun _ : Fin n => ([] : List (Fin m))) v).pre
        [0, 0, 2*v.val] (fun _ => 0) := by
  let lo := 2*n+1
  let w := 2*n+3
  have hw : 2*n+3 < 2 ^ w := Nat.lt_two_pow_self
  have hv := v.isLt
  refine ⟨w, lo, ?_, by rw [Nat.zero_add], adjacencyAt_empty (fun _ _ => rfl), by dsimp [lo]; omega, by omega⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
