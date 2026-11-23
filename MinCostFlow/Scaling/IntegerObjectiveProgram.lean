module

public import MinCostFlow.Scaling.ObjectiveScanProgram
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Computing the full integer objective

Read the graph header and invoke the linear objective scan on its complete
edge array and the corresponding unsigned flow. The returned signed pair
is exactly the `integerObjective` used by the bottleneck threshold test.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,flow,heap]`. -/
def integerObjectiveBody (scan : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 4 scan [.bin .add (.reg 0) (.const 2),.reg 1,.reg 3,.reg 2] ;;
  .ret (.reg 4)

/-- Header reader followed by the exact objective scan. -/
def integerObjectiveModule (b : ℕ) : List Stmt :=
  integerObjectiveBody (b+1) :: objectiveScanModule (b+1)

/-- Exact full-graph objective, with a fitting absolute-product budget. -/
def integerObjectiveContract (w : ℕ) (J : Circulation) (f : Fin J.m → ℕ) : Contract :=
  let H := heapContract w
    (fun args mem => ∃ a flow heap,args=[a,flow,heap] ∧ ListAt mem a J.solverWords ∧
      ListAt mem flow (List.ofFn f) ∧ a+J.solverWords.length ≤ heap ∧ flow+J.m ≤ heap ∧
      (∀ x ∈ J.solverWords,x<2^w) ∧ (∀ e,f e<2^w) ∧
      objectiveScanMass J f (List.finRange J.m)<2^w ∧ 8<2^w)
    (fun _ _ _ => True) (fun _ _ => 500*J.m+250) (fun _ _ => 4*J.m+2)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧
      ret=heapArg args+4*J.m+2 ∧
      ListAt mem' (ret-2) (encodeInt (J.integerObjective (fun e => (f e : ℤ)))) }

/-- Reading the header and computing the objective uses no randomness. -/
theorem integerObjectiveModule_noRand (b : ℕ) : ∀ body ∈ integerObjectiveModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [integerObjectiveBody,Stmt.NoRand,and_self]
  · exact objectiveScanModule_noRand _ body hb

/-- The machine writes exactly the model's integer objective and preserves
both graph and flow arrays, at explicit linear cost. -/
theorem integerObjective_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (integerObjectiveModule b)) (J : Circulation) (f : Fin J.m → ℕ) :
    MeetsContract w p b (integerObjectiveContract w J f) := by
  have hk := objectiveScan_meetsContract (w := w) (hasAt_tail hp) J f (List.finRange J.m)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,flow,heap,rfl,hat,hflow,hend,hfend,hinput,hf,hbudget,hw⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(4*J.m+2)<2^w at hs
  have hh : heap<2^w := by omega
  have hm : J.m<2^w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hfword : flow<2^w := by omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hend; omega
  have ha2 : a+2<2^w := by rw [J.solverWords_length] at hend; omega
  have hM := (solver_header_at J hat).2
  have hedge : ListAt mem (a+2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
    have h := (listAt_cons.mp (listAt_cons.mp hat).2).2
    simpa only [Nat.add_assoc] using h
  have hflow' : ListAt mem flow ((List.finRange J.m).map f) := by
    simpa only [List.ofFn_eq_map] using hflow
  apply runs_start_le
  unfold integerObjectiveBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hk (vs := [a+2,flow,J.m,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · refine ⟨⟨a+2,flow,heap,by simp only [List.length_finRange],hedge,hflow',?_,?_,?_,hbudget,hw⟩,hz,?_⟩
    · rw [J.solverWords_length] at hend
      simp only [List.length_finRange]; omega
    · simpa only [List.length_finRange] using hfend
    · intro e _
      exact ⟨hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords])),hf e⟩
    · change heap+(4*(List.finRange J.m).length+2)<2^w
      simpa only [List.length_finRange] using hs
  · intro ret memR posR hpost
    obtain ⟨⟨hlo,hhi,hframe,hzR,_⟩,hret,hvalue⟩ := hpost
    change heap≤ret at hlo
    change ret≤heap+(4*(List.finRange J.m).length+2) at hhi
    change ret=heap+4*(List.finRange J.m).length+2 at hret
    simp only [List.length_finRange] at hhi hret
    change (∀ x<heap,memR x=mem x) at hframe
    change ZeroFrom memR ret at hzR
    change ListAt memR (ret-2) (encodeInt (objectiveScan J f (List.finRange J.m))) at hvalue
    have hr : ret<2^w := by omega
    refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
    · change (heap≤ret ∧ ret≤heap+(4*J.m+2) ∧ (∀ x<heap,memR x=mem x) ∧ ZeroFrom memR ret ∧ True) ∧
        ret=heap+4*J.m+2 ∧ ListAt memR (ret-2) (encodeInt (J.integerObjective (fun e => (f e : ℤ))))
      rw [objectiveScan_finRange] at hvalue
      exact ⟨⟨hlo,hhi,hframe,hzR,True.intro⟩,hret,hvalue⟩
    · simp only [integerObjectiveContract,objectiveScanContract,heapContract,List.length_finRange,
        argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      omega

end MinCostFlow.Scaling.Machine
