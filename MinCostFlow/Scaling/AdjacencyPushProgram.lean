module

public import MinCostFlow.Scaling.AdjacencyLayout
public import MinCostFlow.Scaling.IndexListConsProgram
public import MinCostFlow.Scaling.WordPairStoreProgram
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Pushing one edge onto a vertex's adjacency list

Positive-flow adjacency assembly prepends the current edge to its tail's
list. This procedure reads that vertex's head and length, allocates one
immutable node, and updates the two head cells. It changes no other old
cell, preserves all list nodes, uses two fresh words, and costs at most 120.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[vertex,edgeIndex,heads,heap]`. The same pair writer allocates
the node and then updates the existing head record. -/
def adjacencyPushBody (writer : ℕ) : Stmt :=
  .assign 4 (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 0))) ;;
  .call 5 writer [.reg 1, .load (.reg 4), .reg 3] ;;
  .call 6 writer [.reg 3, .bin .add (.load (.bin .add (.reg 4) (.const 1))) (.const 1), .reg 4] ;;
  .ret (.reg 5)

/-- One adjacency update and the existing pair-writing procedure. -/
def adjacencyPushModule (b : ℕ) : List Stmt := [adjacencyPushBody (b+1), wordPairBody]

/-- The entire head table precedes the node range, and the new length fits. -/
def adjacencyPushContract (w lo : ℕ) {n m : ℕ} (out : Fin n → List (Fin m))
    (v : Fin n) (e : Fin m) : Contract where
  pre args mem := ∃ heads heap, args = [v.val, e.val, heads, heap] ∧
    AdjacencyAt mem heads lo heap out ∧ heads+2*n ≤ lo ∧ lo ≤ heap ∧
    0 < heap ∧ (out v).length+1 < 2 ^ w ∧ ZeroFrom mem heap ∧ heap+2 < 2 ^ w
  post args mem ret mem' := ret = heapArg args+2 ∧
    AdjacencyAt mem' (args.getD 2 0) lo ret (Function.update out v (e :: out v)) ∧
    ZeroFrom mem' ret ∧
    ∀ x < heapArg args, x ≠ args.getD 2 0+2*v.val → x ≠ args.getD 2 0+2*v.val+1 → mem' x = mem x
  cost _ _ := 120

/-- Adjacency pushes use no random instructions. -/
theorem adjacencyPushModule_noRand (b : ℕ) : ∀ body ∈ adjacencyPushModule b, body.NoRand := by
  intro body hb
  simp only [adjacencyPushModule, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · simp only [adjacencyPushBody, Stmt.NoRand, and_self]
  · exact wordPairBody_noRand

/-- The update computes precisely a vertex-list cons, preserving every
other old cell and returning the exact two-word allocation. -/
theorem adjacencyPush_meetsContract {w b lo n m : ℕ} {p : Program}
    (hp : p.HasAt b (adjacencyPushModule b)) (out : Fin n → List (Fin m))
    (v : Fin n) (e : Fin m) : MeetsContract w p b (adjacencyPushContract w lo out v e) := by
  have hpair : p.HasAt (b+1) wordPairModule := by
    intro i hi
    have hi0 : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [adjacencyPushModule, wordPairModule, List.getElem_cons_succ,
      List.getElem_cons_zero, Nat.add_zero] using hp 1 (by simp [adjacencyPushModule])
  have hkC := indexListCons_meetsContract (w := w) (lo := lo) hpair e (out v)
  have hkW := wordPairStore_meetsContract (w := w) hpair
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨heads, heap, rfl, hat, hheadsEnd, hlo, hpositive, hlength, hzero, hspace⟩ := hpre
  obtain ⟨tail, hhead, hlist⟩ := hat v
  let cell := heads+2*v.val
  have htail : mem cell = tail := by
    have h := hhead 0 (by change 0 < 2; decide)
    change mem (cell+0) = tail at h
    simpa only [Nat.add_zero] using h
  have hlen : mem (cell+1) = (out v).length := hhead 1 (by change 1 < 2; decide)
  have hv := v.isLt
  have hcellEnd : cell+2 ≤ lo := by dsimp [cell]; omega
  have hcell : cell < 2 ^ w := by omega
  have hcell1 : cell+1 < 2 ^ w := by omega
  have htwoV : 2*v.val < 2 ^ w := by dsimp [cell] at hcell; omega
  have hvWord : v.val < 2 ^ w := hwords _ (by simp)
  have heWord : e.val < 2 ^ w := hwords _ (by simp)
  have hheads : heads < 2 ^ w := hwords _ (by simp)
  have hheap : heap < 2 ^ w := by omega
  have htailWord : tail < 2 ^ w := hlist.pointer_le.trans_lt hheap
  have hlenWord : (out v).length < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  apply runs_start_le
  unfold adjacencyPushBody
  refine runs_seq_assign_le (v := cell) (by eval_expr) ?_
  refine runs_seq_call_le hkC (vs := [e.val, tail, heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨tail, heap, rfl, hpositive, hlo, hlist⟩, hzero, hspace⟩
  · intro next memC posC hpostC
    obtain ⟨⟨_, _, hframeC, hzeroC, hnewList⟩, hnext⟩ := hpostC
    change next = heap+2 at hnext
    change (∀ x < heap, memC x = mem x) at hframeC
    change ZeroFrom memC next at hzeroC
    change IndexListAt memC lo (heap+2) heap (e :: out v) at hnewList
    have hlenC : memC (cell+1) = (out v).length := (hframeC _ (by omega)).trans hlen
    have hnextWord : next < 2 ^ w := by omega
    have hcellSpace : cell+2 < 2 ^ w := by omega
    refine runs_seq_call_le hkW (vs := [heap, (out v).length+1, cell]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨heap, (out v).length+1, cell, rfl, hcellSpace⟩
    · intro _ memW posW hpostW
      obtain ⟨_, hstored, hframeW⟩ := hpostW
      change ListAt memW cell [heap, (out v).length+1] at hstored
      change (∀ x, x < cell ∨ cell+2 ≤ x → memW x = memC x) at hframeW
      have hnodesW : IndexListAt memW lo next heap (e :: out v) := by
        rw [hnext]
        apply hnewList.of_agree
        intro x hx _
        exact hframeW x (Or.inr (by omega))
      have htableW : AdjacencyAt memW heads lo next (Function.update out v (e :: out v)) := by
        refine hat.update v (e :: out v) heap hheadsEnd (by omega) ?_ hnodesW ?_ ?_
        · exact hstored
        · intro x hx hxheap
          exact (hframeW x (Or.inr (by omega))).trans (hframeC x hxheap)
        · intro x hx hx0 hx1
          apply (hframeW x ?_).trans (hframeC x (by omega))
          change x ≠ cell at hx0
          change x ≠ cell+1 at hx1
          omega
      refine runs_ret_le (v := next) (by eval_expr) ?_ ?_
      · change next = heap+2 ∧ AdjacencyAt memW heads lo next (Function.update out v (e :: out v)) ∧
          ZeroFrom memW next ∧ ∀ x < heap, x ≠ heads+2*v.val → x ≠ heads+2*v.val+1 → memW x = mem x
        refine ⟨hnext, htableW, ?_, ?_⟩
        · intro x hx
          exact (hframeW x (Or.inr (by omega))).trans (hzeroC x hx)
        · intro x hx hx0 hx1
          apply (hframeW x ?_).trans (hframeC x hx)
          change x ≠ cell at hx0
          change x ≠ cell+1 at hx1
          omega
      · simp only [adjacencyPushContract, indexListConsContract, heapContract,
          wordPairStoreContract, argsSize_cons, argsSize_nil, Expr.size_bin,
          Expr.size_load, Expr.size_reg, Expr.size_const]; omega

/-- Empty adjacency initialization supplies all push premises simultaneously
for every valid vertex and edge index at a sufficiently large width. -/
theorem exists_adjacencyPush_pre {n m : ℕ} (v : Fin n) (e : Fin m) :
    ∃ w lo, (∀ x ∈ [v.val, e.val, 0, lo], x < 2 ^ w) ∧
      (adjacencyPushContract w lo (fun _ : Fin n => ([] : List (Fin m))) v e).pre
        [v.val, e.val, 0, lo] (fun _ => 0) := by
  let lo := 2*n+1
  let w := m+2*n+10
  have hw : m+2*n+10 < 2 ^ w := Nat.lt_two_pow_self
  have hv := v.isLt
  have he := e.isLt
  refine ⟨w, lo, ?_, 0, lo, rfl, adjacencyAt_empty (fun _ _ => rfl),
    by dsimp [lo]; omega, le_rfl, by dsimp [lo]; omega,
    by change 0+1 < 2 ^ w; omega, (fun _ _ => rfl), ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> (try dsimp [lo]) <;> omega
  · dsimp [lo]
    omega

end MinCostFlow.Scaling.Machine
