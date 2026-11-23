module

public import MinCostFlow.Scaling.CapacityCollectEdgesProgram
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# The complete capacity candidate collection

Read the graph's edge count and scan its records. The output is exactly
`List.ofFn J.capacity`, the unsorted candidate list in `bottleneckSearch`.
The source graph remains unchanged and the candidates use one word per edge.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,heap]`. -/
def capacityCollectBody (scan : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 3 scan [.bin .add (.reg 0) (.const 2),.reg 2,.reg 1] ;;
  .ret (.reg 3)

/-- Collection entry followed by the record scan. -/
def capacityCollectModule (b : ℕ) : List Stmt := capacityCollectBody (b+1) :: capacityCollectEdgesModule (b+1)

/-- The exact original-order candidate list is written at the old heap. -/
def capacityCollectContract (w : ℕ) (J : Circulation) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap,args = [a,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length ≤ heap ∧ (∀ x ∈ J.solverWords,x < 2^w) ∧ 8 < 2^w)
    (fun args _ mem' => ListAt mem' (heapArg args) (List.ofFn J.capacity))
    (fun _ _ => 80*J.m+100) (fun _ _ => J.m)
  { C with post := fun args mem ret mem' => C.post args mem ret mem' ∧ ret=heapArg args+J.m }

/-- The entry and scan have no random instruction. -/
theorem capacityCollectModule_noRand (b : ℕ) : ∀ body ∈ capacityCollectModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityCollectBody,Stmt.NoRand,and_self]
  · have he : body = capacityCollectEdgesBody (b+1) := by simpa only [capacityCollectEdgesModule,List.mem_singleton] using hb
    subst body
    exact capacityCollectEdgesBody_noRand _

/-- Capacity collection computes the model's full candidate list with exact
allocation, explicit linear cost, and source-graph preservation. -/
theorem capacityCollect_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (capacityCollectModule b)) (J : Circulation) :
    MeetsContract w p b (capacityCollectContract w J) := by
  have hk := capacityCollectEdges_meetsContract (w := w) (hasAt_tail hp) J (List.finRange J.m)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,heap,rfl,hat,hend,hinput,hw⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+J.m < 2^w at hs
  have hh : heap < 2^w := by omega
  have hm : J.m < 2^w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have ha1 : a+1 < 2^w := by rw [J.solverWords_length] at hend; omega
  have ha2 : a+2 < 2^w := by rw [J.solverWords_length] at hend; omega
  have hM := (solver_header_at J hat).2
  have hedge : ListAt mem (a+2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
    have h := (listAt_cons.mp (listAt_cons.mp hat).2).2
    simpa only [Nat.add_assoc] using h
  apply runs_start_le
  unfold capacityCollectBody
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hk (vs := [a+2,J.m,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · refine ⟨⟨a+2,heap,by simp only [List.length_finRange],hedge,?_,?_,hw⟩,hz,?_⟩
    · rw [List.length_finRange]
      rw [J.solverWords_length] at hend
      omega
    · intro e _
      exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
    · change heap+(List.finRange J.m).length < 2^w
      simpa only [List.length_finRange] using hs
  · intro ret memR posR hpostR
    obtain ⟨⟨_,_,hframe,hzR,hatR⟩,hret⟩ := hpostR
    change ret=heap+(List.finRange J.m).length at hret
    rw [List.length_finRange] at hret
    change (∀ x < heap,memR x = mem x) at hframe
    change ZeroFrom memR ret at hzR
    change ListAt memR heap ((List.finRange J.m).map J.capacity) at hatR
    have harray : ListAt memR heap (List.ofFn J.capacity) := by
      simpa only [List.ofFn_eq_map] using hatR
    have hr : ret < 2^w := by omega
    refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
    · change (heap ≤ ret ∧ ret ≤ heap+J.m ∧ (∀ x < heap,memR x = mem x) ∧
        ZeroFrom memR ret ∧ ListAt memR heap (List.ofFn J.capacity)) ∧ ret=heap+J.m
      exact ⟨⟨by omega,by omega,hframe,hzR,harray⟩,hret⟩
    · simp only [capacityCollectContract,capacityCollectEdgesContract,heapContract,List.length_finRange,
        argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      omega

/-- Multiplier two on the source encoding supplies every collection premise
simultaneously in canonical graph memory. -/
theorem capacityCollect_pre_wordSize (J : Circulation) :
    (∀ x ∈ [0,J.solverWords.length],x < 2^wordSize 2 J.solverWords) ∧
      (capacityCollectContract (wordSize 2 J.solverWords) J).pre
        [0,J.solverWords.length] (initMem J.solverWords) := by
  let base := J.solverWords.length+J.solverWords.foldr max 0+2
  have hlen := J.solverWords_length
  have hbase : 4+5*J.m ≤ base := by dsimp only [base]; omega
  have hbase4 : 4 ≤ base := by omega
  have hlinear : J.solverWords.length+J.m ≤ 2*base := by omega
  have htwo : 2*base ≤ base^2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right base (show 2 ≤ base by omega)
  have hmin : 16 ≤ base^2 := by simpa only [pow_two] using Nat.mul_le_mul hbase4 hbase4
  have hp := pow_lt_two_pow_wordSize (by decide : 1 ≤ 2) J.solverWords
  change base^2 < 2^wordSize 2 J.solverWords at hp
  have hspace := (hlinear.trans htwo).trans_lt hp
  refine ⟨?_,⟨0,J.solverWords.length,rfl,listAt_initMem _,by omega,
    (fun x hx => lt_two_pow_wordSize_of_mem (by decide) hx),by omega⟩,zeroFrom_initMem _,hspace⟩
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
