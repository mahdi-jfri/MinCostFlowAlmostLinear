module

public import MinCostFlow.Scaling.CapacitySolverModel
public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.Scaling.ScaledCapacityProgram
public import MinCostFlow.Scaling.WordFiveProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Edge records for the scaled capacity-rounded instance

Definition C.11's scaled capacity changes only the capacity field of an
edge. Share the rounding power and unit across the scan, call the proved
scalar procedure for each capacity, then write the five-word record.
The result is exactly the model's scaled rounded edge block.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[source,count,m,B,m^20,capacityUnit m B,heap]`. -/
def capacityScaledEdgesBody (self scalar writer : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 6))
    (.call 7 scalar [.load (.bin .add (.reg 0) (.const 2)),.reg 3,.reg 4,.reg 5] ;;
     .call 8 writer [.load (.reg 0),.load (.bin .add (.reg 0) (.const 1)),.reg 7,
       .load (.bin .add (.reg 0) (.const 3)),.load (.bin .add (.reg 0) (.const 4)),.reg 6] ;;
     .call 9 self [.bin .add (.reg 0) (.const 5),.bin .sub (.reg 1) (.const 1),
       .reg 2,.reg 3,.reg 4,.reg 5,.reg 8] ;;
     .ret (.reg 9))

/-- The scan, scalar capacity operation, and shared record writer. -/
def capacityScaledEdgesModule (b : ℕ) : List Stmt :=
  [capacityScaledEdgesBody b (b+1) (b+2),scaledCapacityBody,wordFiveBody]

/-- The scaled rounded record retains endpoints and signed cost words. -/
theorem capacityScaled_edgeWords (J : Circulation) (B : ℕ) (e : Fin J.m) :
    (J.scaledRoundedInstance B).solverEdgeWords e =
      [(J.tail e).val,(J.head e).val,scaledCapacity J.m B (J.capacity e),
        if J.cost e < 0 then 1 else 0,(J.cost e).natAbs] := by
  rfl

/-- The common source block precedes fresh records; one clipping product
budget covers every scalar invocation. -/
def capacityScaledEdgesContract (w : ℕ) (J : Circulation) (B : ℕ) (es : List (Fin J.m)) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap,args = [a,es.length,J.m,B,J.m^20,capacityUnit J.m B,heap] ∧
      ListAt mem a (es.flatMap J.solverEdgeWords) ∧ a+5*es.length ≤ heap ∧
      (∀ e ∈ es,∀ x ∈ J.solverEdgeWords e,x < 2^w) ∧ B*J.m^20 < 2^w ∧ 8 < 2^w)
    (fun args _ mem' => ListAt mem' (heapArg args)
      (es.flatMap (J.scaledRoundedInstance B).solverEdgeWords))
    (fun _ _ => 200*es.length+20) (fun _ _ => 5*es.length)
  { C with post := fun args mem ret mem' => C.post args mem ret mem' ∧ ret = heapArg args+5*es.length }

/-- All scan procedures have no random instruction. -/
theorem capacityScaledEdgesModule_noRand (b : ℕ) :
    ∀ body ∈ capacityScaledEdgesModule b,body.NoRand := by
  intro body hb
  simp only [capacityScaledEdgesModule,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl
  · simp only [capacityScaledEdgesBody,Stmt.NoRand,and_self]
  · exact scaledCapacityBody_noRand
  · exact wordFiveBody_noRand

/-- The scan computes the scaled rounded edge block with exact fresh
allocation and linear machine cost. -/
theorem capacityScaledEdges_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (capacityScaledEdgesModule b)) (J : Circulation) (B : ℕ) (es : List (Fin J.m)) :
    MeetsContract w p b (capacityScaledEdgesContract w J B es) := by
  have hscalar : p.HasAt (b+1) scaledCapacityModule := by
    intro i hi
    have hi0 : i = 0 := by change i<1 at hi; omega
    subst i
    simpa only [scaledCapacityModule,capacityScaledEdgesModule,List.getElem_cons_succ,
      List.getElem_cons_zero,Nat.add_zero] using hp 1 (by simp [capacityScaledEdgesModule])
  have hwriter : p.HasAt (b+2) wordFiveModule := by
    intro i hi
    have hi0 : i = 0 := by change i<1 at hi; omega
    subst i
    simpa only [wordFiveModule,capacityScaledEdgesModule,List.getElem_cons_succ,
      List.getElem_cons_zero,Nat.add_zero] using hp 2 (by simp [capacityScaledEdgesModule])
  have hkW := wordFive_meetsContract (w := w) hwriter
  induction es with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,heap,rfl,_,_,_,_,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+5*0 < 2^w at hs
    have hh : heap < 2^w := by omega
    apply runs_start_le
    unfold capacityScaledEdgesBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap+5*0 ∧ (∀ x < heap,mem x = mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap = heap+5*0
        exact ⟨⟨le_rfl,by omega,fun _ _ => rfl,hz,listAt_nil _ _⟩,by omega⟩
      · simp only [capacityScaledEdgesContract,heapContract,List.length_nil,
          Expr.size_bin,Expr.size_reg,Expr.size_const]; omega
    · simp at hcond
  | cons e es ih =>
    have hkC := scaledCapacity_meetsContract (w := w) hscalar J.m B (J.capacity e)
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,heap,rfl,hat,hend,hinput,hproduct,hw⟩,hz,hs⟩ := hpre
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
    have hpow : J.m^20 < 2^w := hwords _ (by simp)
    have hunit : capacityUnit J.m B < 2^w := hwords _ (by simp)
    have hm : J.m < 2^w := hwords _ (by simp)
    have hlen : (e::es).length < 2^w := hwords _ (by simp)
    have hheap5 : heap+5 < 2^w := by simp only [List.length_cons] at hs; omega
    have hheap : heap < 2^w := by omega
    have ha5 : a+5 < 2^w := by simp only [List.length_cons] at hend; omega
    have ha : a < 2^w := by omega
    have ha1 : a+1 < 2^w := by omega
    have ha2 : a+2 < 2^w := by omega
    have ha3 : a+3 < 2^w := by omega
    have ha4 : a+4 < 2^w := by omega
    have hscaled : scaledCapacity J.m B (J.capacity e) < 2^w :=
      ((min_le_left _ _).trans (Nat.div_le_self _ _)).trans_lt hcapWord
    apply runs_start_le
    unfold capacityScaledEdgesBody
    wram_step
    · simp at hcond
    · refine runs_seq_call_le hkC (vs := [J.capacity e,B,J.m^20,capacityUnit J.m B])
        (by eval_expr) (by wram_words) ⟨rfl,hproduct⟩ ?_
      intro value memC posC hpostC
      obtain ⟨hmemC,hvalue⟩ := hpostC
      subst memC
      subst value
      refine runs_seq_call_le hkW (vs := [(J.tail e).val,(J.head e).val,scaledCapacity J.m B (J.capacity e),
        if J.cost e < 0 then 1 else 0,(J.cost e).natAbs,heap]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨_,_,_,_,_,heap,rfl⟩,hz,hheap5⟩
      · intro next memW posW hpostW
        obtain ⟨⟨_,_,hframeW,hzW,hatW⟩,hnext⟩ := hpostW
        change next = heap+5 at hnext
        change (∀ x < heap,memW x = mem x) at hframeW
        change ZeroFrom memW next at hzW
        change ListAt memW heap ((J.scaledRoundedInstance B).solverEdgeWords e) at hatW
        have htailW : ListAt memW (a+5) (es.flatMap J.solverEdgeWords) :=
          htail.of_agree_below (by rw [J.solverEdgeRecords_length]; simp only [List.length_cons] at hend; omega) hframeW
        have hnword : next < 2^w := by omega
        have htlen : es.length < 2^w := by simp only [List.length_cons] at hlen; omega
        refine runs_seq_call_le ih (vs := [a+5,es.length,J.m,B,J.m^20,capacityUnit J.m B,next]) ?_ (by wram_words) ?_ ?_
        · have heq : (e::es).length-1 = es.length := rfl
          rw [← heq]
          eval_expr
        · refine ⟨⟨a+5,next,rfl,htailW,?_,(fun e' he' => hinput e' (List.mem_cons_of_mem e he')),
            hproduct,hw⟩,hzW,?_⟩
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
          change ListAt memR next (es.flatMap (J.scaledRoundedInstance B).solverEdgeWords) at hatR
          have hrword : ret < 2^w := by simp only [List.length_cons] at hs; omega
          refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · change (heap ≤ ret ∧ ret ≤ heap+5*(e::es).length ∧ (∀ x < heap,memR x = mem x) ∧
              ZeroFrom memR ret ∧ ListAt memR heap ((e::es).flatMap (J.scaledRoundedInstance B).solverEdgeWords)) ∧
              ret = heap+5*(e::es).length
            refine ⟨⟨by omega,by simp only [List.length_cons]; omega,?_,hzR,?_⟩,
              by simp only [List.length_cons]; omega⟩
            · intro x hx
              exact (hframeR x (by omega)).trans (hframeW x hx)
            · rw [List.flatMap_cons]
              apply listAt_append.mpr
              refine ⟨hatW.of_agree_below (h₀ := next) (by change heap+5 ≤ next; omega) hframeR,?_⟩
              simpa only [Circulation.solverEdgeWords,List.length_cons,List.length_nil,Nat.reduceAdd,hnext] using hatR
          · simp only [capacityScaledEdgesContract,heapContract,scaledCapacityContract,wordFiveContract,
              List.length_cons,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
            omega

end MinCostFlow.Scaling.Machine
