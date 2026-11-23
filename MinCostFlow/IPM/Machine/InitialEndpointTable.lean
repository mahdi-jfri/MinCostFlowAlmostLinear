module

public import MinCostFlow.IPM.Machine.InitialCapacities
public import MinCostFlow.IPM.Machine.InitialEndpointScan
public import MinCostFlow.IPM.Machine.InitialDeficitModel
import MinCostFlow.Scaling.SolverInputLayout
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic

/-!
# Reading one midpoint endpoint table from the solver input

The initialization in Lemma 4.12 (Chen et al., arXiv:2203.00671v2,
page 31 and Appendix B.1 page 92) computes the routing of the original
midpoint flow before adding auxiliary edges. This entry reads the
solver header, selects its tail or head fields, and invokes the verified
unsigned accumulator. The output is exactly outgoing or incoming
capacity at each vertex, not a newly assumed deficit oracle.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- Decode an endpoint field at offset two or three. -/
theorem solver_endpoint_at (J : Circulation) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a J.solverWords) (heads : Bool) (e : Fin J.m) :
    mem (a+(if heads then 3 else 2)+5*e.val) =
      if heads then (J.head e : ℕ) else (J.tail e : ℕ) := by
  have hh := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).2.2
  cases heads
  · simpa only [Bool.false_eq_true,↓reduceIte,Circulation.solverEdgeWords,List.getD_cons_zero,
      Nat.add_zero,Nat.add_assoc] using hh e ⟨0,by decide⟩
  · have he := hh e ⟨1,by decide⟩
    simpa only [↓reduceIte,Circulation.solverEdgeWords,List.getD_cons_succ,List.getD_cons_zero,
      show a+(2+5*e.val+1) = a+3+5*e.val by omega] using he

/-- The total-capacity fit premise can be read directly from input words. -/
theorem solver_capacity_sum (J : Circulation) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a J.solverWords) :
    (∑ i ∈ Finset.range J.m, mem (a+4+5*i)) = ∑ e : Fin J.m, J.capacity e := by
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro e _
  exact solver_capacity_at J mem a hat e

/-- Arguments `[input,heap]`. The choice of tails or heads is static. -/
def initialEndpointTableBody (scan : ℕ) (heads : Bool) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 4 scan [.bin .add (.reg 0) (.const (if heads then 3 else 2)),
    .bin .add (.reg 0) (.const 4),.reg 3,.reg 2,.reg 1] ;;
  .ret (.reg 4)

/-- One header reader and the exact accumulator. -/
def initialEndpointTableModule (b : ℕ) (heads : Bool) : List Stmt :=
  [initialEndpointTableBody (b+1) heads] ++ initialEndpointScanModule

/-- The exact endpoint table, in `n` cells, with linear scan cost. -/
def initialEndpointTableContract (w : ℕ) (J : Circulation) (heads : Bool) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap, args = [a,heap] ∧ 0 < J.m ∧
      ListAt mem a J.solverWords ∧ a+J.solverWords.length ≤ heap ∧
      (∀ x ∈ J.solverWords, x < 2^w) ∧ (∑ e : Fin J.m, J.capacity e) < 2^w)
    (fun args _ mem' => ∀ v < J.n, mem' (heapArg args+v) =
      if heads then incomingCapacity J v else outgoingCapacity J v)
    (fun _ _ => 80*J.m+130) (fun _ _ => J.n)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧ v = heapArg args+J.n }

/-- The header reader and accumulator use no randomness. -/
theorem initialEndpointTableModule_noRand (b : ℕ) (heads : Bool) :
    ∀ body ∈ initialEndpointTableModule b heads, body.NoRand := by
  intro body hb
  simp only [initialEndpointTableModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [initialEndpointTableBody,Stmt.NoRand]
  · simp only [initialEndpointScanModule,List.mem_singleton] at hb
    subst body
    exact initialEndpointScanBody_noRand

/-- Both endpoint choices compute the existing model's exact capacity
sum table, with all input and scratch-memory premises explicit. -/
theorem initialEndpointTable_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (heads : Bool) (hp : p.HasAt b (initialEndpointTableModule b heads)) (J : Circulation) :
    MeetsContract w p b (initialEndpointTableContract w J heads) := by
  have hscan : p.HasAt (b+1) initialEndpointScanModule := Num.hasAt_append_right hp
  have hk := initialEndpointScan_meetsContract hw hscan
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨a,heap,rfl,hm,hat,hend,hinput,htotal⟩,hzero,hspace⟩ := hpre
  change heap+J.n < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have hlen := J.solverWords_length
  have hheader := (Scaling.Machine.solverWords_at_iff J mem a).mp hat
  have hN := hheader.1
  have hM := hheader.2.1
  have hnw : J.n < 2^w := hinput _ List.mem_cons_self
  have hmw : J.m < 2^w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hheap : heap < 2^w := hwords _ (by simp)
  have ha1 : a+1 < 2^w := by omega
  have ha4 : a+4 < 2^w := by omega
  have hoff : (if heads then 3 else 2) < 2^w := by cases heads <;> simp <;> omega
  have haoff : a+(if heads then 3 else 2) < 2^w := by cases heads <;> simp <;> omega
  have hsource : ∀ i < J.m,
      a+(if heads then 3 else 2)+5*i < heap ∧ a+4+5*i < heap ∧
      mem (a+(if heads then 3 else 2)+5*i) < J.n := by
    intro i hi
    refine ⟨?_,by omega,?_⟩
    · cases heads <;> simp <;> omega
    · rw [solver_endpoint_at J mem a hat heads ⟨i,hi⟩]
      cases heads
      · exact (J.tail ⟨i,hi⟩).isLt
      · exact (J.head ⟨i,hi⟩).isLt
  have htot : (∑ i ∈ Finset.range J.m, mem (a+4+5*i)) < 2^w := by
    rw [solver_capacity_sum J mem a hat]
    exact htotal
  apply runs_start_le
  unfold initialEndpointTableBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hk (vs := [a+(if heads then 3 else 2),a+4,J.m,J.n,heap])
    (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨_,_,_,_,_,rfl,hsource,htot⟩,hzero,hspace⟩
  · intro v mem' pos' hout
    obtain ⟨⟨hlo,hhi,hframe,hfresh,htable⟩,hv⟩ := hout
    change v = heap+J.n at hv
    have hvw : v < 2^w := by omega
    refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
    · change (heap ≤ v ∧ v ≤ heap+J.n ∧ (∀ x < heap, mem' x = mem x) ∧
        ZeroFrom mem' v ∧ _) ∧ v = heap+J.n
      refine ⟨⟨hlo,hhi,hframe,hfresh,?_⟩,hv⟩
      intro x hx
      have hh := htable x hx
      change mem' (heap+x) = initialEndpointSum
        (fun i => mem (a+(if heads then 3 else 2)+5*i)) (fun i => mem (a+4+5*i)) J.m x at hh
      change mem' (heap+x) = if heads then incomingCapacity J x else outgoingCapacity J x
      rw [hh]
      cases heads
      · exact initialEndpointSum_outgoing J _ _
          (fun e => solver_endpoint_at J mem a hat false e)
          (fun e => solver_capacity_at J mem a hat e) x
      · exact initialEndpointSum_incoming J _ _
          (fun e => solver_endpoint_at J mem a hat true e)
          (fun e => solver_capacity_at J mem a hat e) x
    · simp only [initialEndpointTableContract,initialEndpointScanContract,heapContract,
        Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,argsSize_cons,argsSize_nil,
        List.getD_cons_zero,List.getD_cons_succ]
      omega

end MinCostFlow.IPM.Machine
