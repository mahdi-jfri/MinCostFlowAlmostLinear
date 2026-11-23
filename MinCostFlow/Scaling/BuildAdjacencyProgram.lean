module

public import MinCostFlow.Scaling.AdjacencyEdgesProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Constructing all positive-flow adjacency lists

The label and cycle models build adjacency by a single edge scan from
empty lists. A fresh zero heap initializes the pointer/length table. This
procedure reserves two words per vertex and one gap cell for null, then
runs the exact edge scan. It computes `Circulation.buildAdjacency`, costs
at most `300*m+150` steps, and uses at most `2*n+1+2*m` fresh words.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,flow,heap]`. The adjacency heads start at the old heap. -/
def buildAdjacencyBody (scan : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 5 (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 3))) (.const 1)) ;;
  .call 6 scan [.bin .add (.reg 0) (.const 2), .reg 1, .reg 4, .const 0, .reg 2, .reg 5] ;;
  .ret (.reg 6)

/-- Initialization followed by the complete conditional edge scan. -/
def buildAdjacencyModule (b : ℕ) : List Stmt :=
  buildAdjacencyBody (b+1) :: adjacencyEdgesModule (b+1)

/-- The graph and unsigned flow arrays precede fresh adjacency storage.
The input integer flow is nonnegative, as for feasible solver outputs. -/
def buildAdjacencyContract (w : ℕ) (J : Circulation) (f : Fin J.m → ℤ) : Contract where
  pre args mem := ∃ a flow heap, args = [a, flow, heap] ∧
    ListAt mem a J.solverWords ∧ ListAt mem flow (List.ofFn (fun e => (f e).toNat)) ∧
    a+J.solverWords.length ≤ heap ∧ flow+J.m ≤ heap ∧
    (∀ e, 0 ≤ f e ∧ (f e).toNat < 2 ^ w) ∧ ZeroFrom mem heap ∧
    heap+2*J.n+1+2*J.m < 2 ^ w ∧ 8 < 2 ^ w
  post args mem ret mem' := heapArg args+2*J.n+1 ≤ ret ∧
    ret ≤ heapArg args+2*J.n+1+2*J.m ∧
    AdjacencyAt mem' (heapArg args) (heapArg args+2*J.n+1) ret (J.buildAdjacency f) ∧
    ZeroFrom mem' ret ∧ ∀ x < heapArg args, mem' x = mem x
  cost _ _ := 300*J.m+150

/-- Complete adjacency construction uses no random instructions. -/
theorem buildAdjacencyModule_noRand (b : ℕ) : ∀ body ∈ buildAdjacencyModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [buildAdjacencyBody, Stmt.NoRand, and_self]
  · exact adjacencyEdgesModule_noRand _ body hb

/-- The initialized machine scan computes all of `buildAdjacency` with an
explicit linear cost, fresh-space bound, and preserved input memory. -/
theorem buildAdjacency_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (buildAdjacencyModule b)) (J : Circulation) (f : Fin J.m → ℤ) :
    MeetsContract w p b (buildAdjacencyContract w J f) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, flow, heap, rfl, hat, hflow, hend, hflowend, hvalues, hzero, hspace, hw⟩ := hpre
  let lo := heap+2*J.n+1
  have hk := adjacencyEdges_meetsContract (w := w) (lo := lo) (hasAt_tail hp) J f
    (fun _ => []) (List.finRange J.m) 0 0
  have hsize := J.solverWords_length
  have hN : mem a = J.n := by
    simpa only [Circulation.solverWords, List.getElem_cons_zero, Nat.add_zero] using
      hat 0 (by rw [hsize]; omega)
  have hM : mem (a+1) = J.m := by
    simpa only [Circulation.solverWords, List.getElem_cons_succ, List.getElem_cons_zero] using
      hat 1 (by rw [hsize]; omega)
  have hedge : ListAt mem (a+2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
    have h := (listAt_cons.mp (listAt_cons.mp hat).2).2
    simpa only [Nat.add_assoc] using h
  have hflow' : ListAt mem flow ((List.finRange J.m).map (fun e => (f e).toNat)) := by
    rwa [← List.ofFn_eq_map]
  have hlo : lo < 2 ^ w := by dsimp [lo]; omega
  have hzeroLo : ZeroFrom mem lo := by
    intro x hx
    exact hzero x (by dsimp [lo] at hx; omega)
  have hn : J.n < 2 ^ w := by omega
  have hm : J.m < 2 ^ w := by omega
  have ha : a < 2 ^ w := by rw [hsize] at hend; omega
  have ha1 : a+1 < 2 ^ w := by rw [hsize] at hend; omega
  have ha2 : a+2 < 2 ^ w := by rw [hsize] at hend; omega
  have hflowWord : flow < 2 ^ w := by omega
  have hheap : heap < 2 ^ w := by omega
  have h2n : 2*J.n < 2 ^ w := by omega
  have hheap2n : heap+2*J.n < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  apply runs_start_le
  unfold buildAdjacencyBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := lo) (by eval_expr) ?_
  refine runs_seq_call_le hk (vs := [a+2, flow, J.m, 0, heap, lo]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · refine ⟨a+2, flow, heap, lo, by simp only [List.length_finRange], hedge, hflow',
      adjacencyAt_empty hzero, ?_, ?_, ?_, le_rfl, ?_, ?_, ?_, ?_, ?_,
      fun e _ => hvalues e, hzeroLo, ?_, hw⟩
    · rw [List.length_finRange]
      rw [hsize] at hend
      omega
    · rw [List.length_finRange]
      exact hflowend
    · dsimp [lo]; omega
    · dsimp [lo]; omega
    · intro v
      exact le_rfl
    · rw [List.length_finRange]; omega
    · rw [List.length_finRange]; omega
    · intro i hi
      simp only [List.getElem_finRange, Fin.val_cast, Nat.zero_add]
    · rw [List.length_finRange]
      exact hspace
  · intro ret memS posS hpostS
    obtain ⟨hretLower, hretUpper, htableS, hzeroS, hframeS⟩ := hpostS
    change lo ≤ ret at hretLower
    change ret ≤ lo+2*(List.finRange J.m).length at hretUpper
    rw [List.length_finRange] at hretUpper
    change AdjacencyAt memS heap lo ret (J.buildAdjacency f) at htableS
    change (∀ x < lo, x < heap ∨ heap+2*J.n ≤ x → memS x = mem x) at hframeS
    have hretWord : ret < 2 ^ w := by dsimp [lo] at hretUpper; omega
    refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
    · change heap+2*J.n+1 ≤ ret ∧ ret ≤ heap+2*J.n+1+2*J.m ∧
        AdjacencyAt memS heap (heap+2*J.n+1) ret (J.buildAdjacency f) ∧
        ZeroFrom memS ret ∧ ∀ x < heap, memS x = mem x
      refine ⟨hretLower, hretUpper, htableS, hzeroS, ?_⟩
      intro x hx
      exact hframeS x (by dsimp [lo]; omega) (Or.inl hx)
    · simp only [buildAdjacencyContract, adjacencyEdgesContract, List.length_finRange,
        argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_load, Expr.size_reg,
        Expr.size_const]; omega

end MinCostFlow.Scaling.Machine
