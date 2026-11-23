module

public import MinCostFlow.Scaling.BottleneckSearch
public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.Scaling.BottleneckCapacityProgram
public import MinCostFlow.Scaling.WordFiveProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Edge records for one bottleneck test graph

Keep a source edge at unit capacity exactly when its positive capacity
meets the threshold. Preserve all endpoints and costs and retain inactive
slots as zero-capacity records. The shared scalar test and five-word writer
compute exactly the model's bottleneck graph edge block.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,count,threshold,heap]`. -/
def bottleneckEdgesBody (self scalar writer : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 3))
    (.call 4 scalar [.load (.bin .add (.reg 0) (.const 2)),.reg 2] ;;
     .call 5 writer [.load (.reg 0),.load (.bin .add (.reg 0) (.const 1)),.reg 4,
       .load (.bin .add (.reg 0) (.const 3)),.load (.bin .add (.reg 0) (.const 4)),.reg 3] ;;
     .call 6 self [.bin .add (.reg 0) (.const 5),.bin .sub (.reg 1) (.const 1),.reg 2,.reg 5] ;;
     .ret (.reg 6))

/-- The scan, scalar capacity operation, and shared record writer. -/
def bottleneckEdgesModule (b : ℕ) : List Stmt :=
  [bottleneckEdgesBody b (b+1) (b+2),bottleneckCapacityBody,wordFiveBody]

/-- The bottleneck record retains endpoints and signed cost words. -/
theorem bottleneck_edgeWords (J : Circulation) (B : ℕ) (e : Fin J.m) :
    (J.bottleneckGraph B).solverEdgeWords e =
      [(J.tail e).val,(J.head e).val,(if 0 < J.capacity e ∧ B ≤ J.capacity e then 1 else 0),
        if J.cost e < 0 then 1 else 0,(J.cost e).natAbs] := by
  rfl

/-- The common source block precedes fresh records; threshold words are
supplied as procedure arguments. -/
def bottleneckEdgesContract (w : ℕ) (J : Circulation) (B : ℕ) (es : List (Fin J.m)) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap,args = [a,es.length,B,heap] ∧
      ListAt mem a (es.flatMap J.solverEdgeWords) ∧ a+5*es.length ≤ heap ∧
      (∀ e ∈ es,∀ x ∈ J.solverEdgeWords e,x < 2^w) ∧ 8 < 2^w)
    (fun args _ mem' => ListAt mem' (heapArg args)
      (es.flatMap (J.bottleneckGraph B).solverEdgeWords))
    (fun _ _ => 200*es.length+20) (fun _ _ => 5*es.length)
  { C with post := fun args mem ret mem' => C.post args mem ret mem' ∧ ret = heapArg args+5*es.length }

/-- All scan procedures have no random instruction. -/
theorem bottleneckEdgesModule_noRand (b : ℕ) :
    ∀ body ∈ bottleneckEdgesModule b,body.NoRand := by
  intro body hb
  simp only [bottleneckEdgesModule,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl
  · simp only [bottleneckEdgesBody,Stmt.NoRand,and_self]
  · exact bottleneckCapacityBody_noRand
  · exact wordFiveBody_noRand

/-- The scan computes the bottleneck edge block with exact fresh
allocation and linear machine cost. -/
theorem bottleneckEdges_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (bottleneckEdgesModule b)) (J : Circulation) (B : ℕ) (es : List (Fin J.m)) :
    MeetsContract w p b (bottleneckEdgesContract w J B es) := by
  have hscalar : p.HasAt (b+1) bottleneckCapacityModule := by
    intro i hi
    have hi0 : i = 0 := by change i<1 at hi; omega
    subst i
    simpa only [bottleneckCapacityModule,bottleneckEdgesModule,List.getElem_cons_succ,
      List.getElem_cons_zero,Nat.add_zero] using hp 1 (by simp [bottleneckEdgesModule])
  have hwriter : p.HasAt (b+2) wordFiveModule := by
    intro i hi
    have hi0 : i = 0 := by change i<1 at hi; omega
    subst i
    simpa only [wordFiveModule,bottleneckEdgesModule,List.getElem_cons_succ,
      List.getElem_cons_zero,Nat.add_zero] using hp 2 (by simp [bottleneckEdgesModule])
  have hkW := wordFive_meetsContract (w := w) hwriter
  induction es with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,heap,rfl,_,_,_,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+5*0 < 2^w at hs
    have hh : heap < 2^w := by omega
    apply runs_start_le
    unfold bottleneckEdgesBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap+5*0 ∧ (∀ x < heap,mem x = mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap = heap+5*0
        exact ⟨⟨le_rfl,by omega,fun _ _ => rfl,hz,listAt_nil _ _⟩,by omega⟩
      · simp only [bottleneckEdgesContract,heapContract,List.length_nil,
          Expr.size_bin,Expr.size_reg,Expr.size_const]; omega
    · simp at hcond
  | cons e es ih =>
    have hkC := bottleneckCapacity_meetsContract (w := w) hscalar (J.capacity e) B
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,heap,rfl,hat,hend,hinput,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+5*(e::es).length < 2^w at hs
    obtain ⟨hhead,htail⟩ := listAt_append.mp hat
    change ListAt mem a (J.solverEdgeWords e) at hhead
    change ListAt mem (a+5) (es.flatMap J.solverEdgeWords) at htail
    have hfields : ∀ j : Fin 5,mem (a+j.val) = (J.solverEdgeWords e).getD j.val 0 := by
      intro j
      rw [List.getD_eq_getElem _ _ (show j.val < (J.solverEdgeWords e).length from j.isLt)]
      exact hhead _ j.isLt
    have ht := hfields ⟨0,by decide⟩
    have hh := hfields ⟨1,by decide⟩
    have hc := hfields ⟨2,by decide⟩
    have hsign := hfields ⟨3,by decide⟩
    have hmag := hfields ⟨4,by decide⟩
    simp only [Circulation.solverEdgeWords,List.getD_cons_succ,List.getD_cons_zero,Nat.add_zero] at ht hh hc hsign hmag
    have htailWord : (J.tail e).val < 2^w := hinput e List.mem_cons_self _ (by simp [Circulation.solverEdgeWords])
    have hheadWord : (J.head e).val < 2^w := hinput e List.mem_cons_self _ (by simp [Circulation.solverEdgeWords])
    have hcapWord : J.capacity e < 2^w := hinput e List.mem_cons_self _ (by simp [Circulation.solverEdgeWords])
    have hsignWord : (if J.cost e < 0 then 1 else 0 : ℕ) < 2^w := by split <;> omega
    have hmagWord : (J.cost e).natAbs < 2^w := hinput e List.mem_cons_self _ (by simp [Circulation.solverEdgeWords])
    have hB : B < 2^w := hwords _ (by simp)
    have hlen : (e::es).length < 2^w := hwords _ (by simp)
    have hheap5 : heap+5 < 2^w := by simp only [List.length_cons] at hs; omega
    have hheap : heap < 2^w := by omega
    have ha5 : a+5 < 2^w := by simp only [List.length_cons] at hend; omega
    have ha : a < 2^w := by omega
    have ha1 : a+1 < 2^w := by omega
    have ha2 : a+2 < 2^w := by omega
    have ha3 : a+3 < 2^w := by omega
    have ha4 : a+4 < 2^w := by omega
    have hscaled : (if 0 < J.capacity e ∧ B ≤ J.capacity e then 1 else 0 : ℕ) < 2^w := by
      split <;> omega
    apply runs_start_le
    unfold bottleneckEdgesBody
    wram_step
    · simp at hcond
    · refine runs_seq_call_le hkC (vs := [J.capacity e,B])
        (by eval_expr) (by wram_words) ⟨rfl,by omega⟩ ?_
      intro value memC posC hpostC
      obtain ⟨hmemC,hvalue⟩ := hpostC
      subst memC
      subst value
      refine runs_seq_call_le hkW (vs := [(J.tail e).val,(J.head e).val,(if 0 < J.capacity e ∧ B ≤ J.capacity e then 1 else 0),
        if J.cost e < 0 then 1 else 0,(J.cost e).natAbs,heap]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨_,_,_,_,_,heap,rfl⟩,hz,hheap5⟩
      · intro next memW posW hpostW
        obtain ⟨⟨_,_,hframeW,hzW,hatW⟩,hnext⟩ := hpostW
        change next = heap+5 at hnext
        change (∀ x < heap,memW x = mem x) at hframeW
        change ZeroFrom memW next at hzW
        change ListAt memW heap ((J.bottleneckGraph B).solverEdgeWords e) at hatW
        have htailW : ListAt memW (a+5) (es.flatMap J.solverEdgeWords) :=
          htail.of_agree_below (by rw [J.solverEdgeRecords_length]; simp only [List.length_cons] at hend; omega) hframeW
        have hnword : next < 2^w := by omega
        have htlen : es.length < 2^w := by simp only [List.length_cons] at hlen; omega
        refine runs_seq_call_le ih (vs := [a+5,es.length,B,next]) ?_ (by wram_words) ?_ ?_
        · have heq : (e::es).length-1 = es.length := rfl
          rw [← heq]
          eval_expr
        · refine ⟨⟨a+5,next,rfl,htailW,?_,(fun e' he' => hinput e' (List.mem_cons_of_mem e he')),
            hw⟩,hzW,?_⟩
          · simp only [List.length_cons] at hend
            omega
          · change next+5*es.length < 2^w
            simp only [List.length_cons] at hs
            omega
        · intro ret memR posR hpostR
          obtain ⟨⟨_,_,hframeR,hzR,hatR⟩,hret⟩ := hpostR
          change ret = next+5*es.length at hret
          change (∀ x < next,memR x = memW x) at hframeR
          change ZeroFrom memR ret at hzR
          change ListAt memR next (es.flatMap (J.bottleneckGraph B).solverEdgeWords) at hatR
          have hrword : ret < 2^w := by simp only [List.length_cons] at hs; omega
          refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · change (heap ≤ ret ∧ ret ≤ heap+5*(e::es).length ∧ (∀ x < heap,memR x = mem x) ∧
              ZeroFrom memR ret ∧ ListAt memR heap ((e::es).flatMap (J.bottleneckGraph B).solverEdgeWords)) ∧
              ret = heap+5*(e::es).length
            refine ⟨⟨by omega,by simp only [List.length_cons]; omega,?_,hzR,?_⟩,
              by simp only [List.length_cons]; omega⟩
            · intro x hx
              exact (hframeR x (by omega)).trans (hframeW x hx)
            · rw [List.flatMap_cons]
              apply listAt_append.mpr
              refine ⟨hatW.of_agree_below (h₀ := next) (by change heap+5 ≤ next; omega) hframeR,?_⟩
              simpa only [Circulation.solverEdgeWords,List.length_cons,List.length_nil,Nat.reduceAdd,hnext] using hatR
          · simp only [bottleneckEdgesContract,heapContract,bottleneckCapacityContract,wordFiveContract,
              List.length_cons,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
            omega

end MinCostFlow.Scaling.Machine
