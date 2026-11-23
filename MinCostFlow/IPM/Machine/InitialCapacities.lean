module

public import MinCostFlow.IPM.Machine.InitialCapacityScan
public import MinCostFlow.Scaling.CirculationInstance
public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.IPM.CapacityPreprocessing
import MinCostFlow.Scaling.SolverInputLayout
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic

/-!
# The original-edge part of Lemma 4.12 initialization

The solver input stores nonnegative upper capacities, zero lower
capacities, and zero demands. Appendix B.1 of Chen et al.,
arXiv:2203.00671v2 (page 92, Lemma 4.12 on page 31), starts by taking
midpoints. The entry below reads the actual solver header and runs the
capacity scan. Its output is the exact integer numerator of each
half-integral midpoint, with denominator two. These numerators also
supply the doubled routing deficits used to create the auxiliary edges.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- The capacity cell of edge `e` in the solver layout. -/
theorem solver_capacity_at (J : Circulation) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a J.solverWords) (e : Fin J.m) :
    mem (a+4+5*e.val) = J.capacity e := by
  have hh := (Scaling.Machine.solverWords_at_iff J mem a).mp hat
  have he := hh.2.2 e ⟨2,by decide⟩
  simpa only [Circulation.solverEdgeWords,List.getD_cons_succ,List.getD_cons_zero,
    show a+(2+5*e.val+2) = a+4+5*e.val by omega] using he

/-- Arguments `[input,heap]`. Read `m`, then scan the capacity fields. -/
def initialCapacitiesBody (scan : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 3 scan [.bin .add (.reg 0) (.const 4),.reg 2,.reg 1] ;;
  .ret (.reg 3)

/-- The entry and its proved capacity scan. -/
def initialCapacitiesModule (b : ℕ) : List Stmt :=
  [initialCapacitiesBody (b+1)] ++ initialCapacityScanModule

/-- The midpoint numerator table of a nonempty circulation instance,
computed from its actual input encoding. Empty instances are handled
before invoking the positive-size IPM initialization. -/
def initialCapacitiesContract (w : ℕ) (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap, args = [a,heap] ∧ 0 < J.m ∧
      ListAt mem a J.solverWords ∧ a+J.solverWords.length ≤ heap ∧
      ∀ x ∈ J.solverWords, x < 2^w)
    (fun args _ mem' => ∀ e : Fin J.m, mem' (heapArg args+e.val) = J.capacity e)
    (fun _ _ => 40*J.m+100) (fun _ _ => J.m)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧ v = heapArg args+J.m }

/-- The complete entry module is deterministic. -/
theorem initialCapacitiesModule_noRand (b : ℕ) :
    ∀ body ∈ initialCapacitiesModule b, body.NoRand := by
  intro body hb
  simp only [initialCapacitiesModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [initialCapacitiesBody,Stmt.NoRand]
  · simp only [initialCapacityScanModule,List.mem_singleton] at hb
    subst body
    exact initialCapacityScanBody_noRand

/-- The actual solver input is scanned in linear time, with exact
allocation and framing. The result is an integer array, so odd
capacities lose no half unit in initialization. -/
theorem initialCapacities_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (hp : p.HasAt b (initialCapacitiesModule b)) (J : Circulation) :
    MeetsContract w p b (initialCapacitiesContract w J) := by
  have hscan : p.HasAt (b+1) initialCapacityScanModule := Num.hasAt_append_right hp
  have hk := initialCapacityScan_meetsContract hw hscan
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨a,heap,rfl,hm,hat,hend,hinput⟩,hzero,hspace⟩ := hpre
  change heap+J.m < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have hlen := J.solverWords_length
  have hM := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).2.1
  have hmw : J.m < 2^w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hheap : heap < 2^w := hwords _ (by simp)
  have ha1 : a+1 < 2^w := by omega
  have ha4 : a+4 < 2^w := by omega
  have hsource : ∀ i < J.m, a+4+5*i < heap ∧ mem (a+4+5*i) < 2^w := by
    intro i hi
    have hidx : 2+5*i+2 < J.solverWords.length := by omega
    have hc := solver_capacity_at J mem a hat ⟨i,hi⟩
    have hh := Scaling.Machine.solverWords_edge_getD J ⟨i,hi⟩ ⟨2,by decide⟩
    simp only [Circulation.solverEdgeWords,List.getD_cons_succ,List.getD_cons_zero] at hh
    rw [List.getD_eq_getElem _ _ hidx] at hh
    refine ⟨by omega,?_⟩
    rw [hc]
    exact hh ▸ hinput _ (List.getElem_mem hidx)
  apply runs_start_le
  unfold initialCapacitiesBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hk (vs := [a+4,J.m,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨a+4,J.m,heap,rfl,hsource⟩,hzero,hspace⟩
  · intro v mem' pos' hout
    obtain ⟨⟨hlo,hhi,hframe,hfresh,hcopy⟩,hv⟩ := hout
    change v = heap+J.m at hv
    have hvw : v < 2^w := by omega
    refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
    · change (heap ≤ v ∧ v ≤ heap+J.m ∧ (∀ x < heap, mem' x = mem x) ∧
        ZeroFrom mem' v ∧ (∀ e : Fin J.m, mem' (heap+e.val) = J.capacity e)) ∧ v = heap+J.m
      refine ⟨⟨hlo,hhi,hframe,hfresh,?_⟩,hv⟩
      intro e
      exact (hcopy e.val e.isLt).trans (solver_capacity_at J mem a hat e)
    · simp only [initialCapacitiesContract,initialCapacityScanContract,heapContract,
        Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,argsSize_cons,argsSize_nil,
        List.getD_cons_zero,List.getD_cons_succ]
      omega

/-- A decoded output entry, divided by two, is exactly the midpoint
in the existing initialization model. This is an equality, not a
floating-point approximation. -/
theorem initialCapacities_midpoint (J : Circulation) (mem' : ℕ → ℕ) (heap : ℕ)
    (hout : ∀ e : Fin J.m, mem' (heap+e.val) = J.capacity e)
    (e : Fin J.toInstance.m) :
    (mem' (heap+e.val) : ℝ)/2 = midpointFlow J.toInstance e := by
  rw [midpointFlow, Circulation.toInstance_edge]
  simp only [Circulation.inputEdge,Int.cast_zero,Int.cast_natCast,zero_add]
  exact congrArg (fun x : ℕ => (x : ℝ)/2) (hout (J.inputIndex e))

end MinCostFlow.IPM.Machine
