module

public import MinCostFlow.Scaling.SolverContract
import WordRAM.Logic
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Collecting the model's capacity candidates from edge records

Read the capacity word of each consecutive five-word record and write a
fresh contiguous natural array. The list order is unchanged. This is the
linear collection step before the bottleneck model's stable merge sort.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[records,count,heap]`. -/
def capacityCollectEdgesBody (self : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 2))
    (.store (.reg 2) (.load (.bin .add (.reg 0) (.const 2))) ;;
     .call 3 self [.bin .add (.reg 0) (.const 5),.bin .sub (.reg 1) (.const 1),
       .bin .add (.reg 2) (.const 1)] ;;
     .ret (.reg 3))

/-- A single recursive record-to-capacity scan. -/
def capacityCollectEdgesModule (b : ℕ) : List Stmt := [capacityCollectEdgesBody b]

/-- Source records precede the fresh candidate array. Only the selected
capacity values are read by this scan. -/
def capacityCollectEdgesContract (w : ℕ) (J : Circulation) (es : List (Fin J.m)) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a heap,args = [a,es.length,heap] ∧
      ListAt mem a (es.flatMap J.solverEdgeWords) ∧ a+5*es.length ≤ heap ∧
      (∀ e ∈ es,J.capacity e < 2^w) ∧ 8 < 2^w)
    (fun args _ mem' => ListAt mem' (heapArg args) (es.map J.capacity))
    (fun _ _ => 80*es.length+20) (fun _ _ => es.length)
  { C with post := fun args mem ret mem' => C.post args mem ret mem' ∧ ret = heapArg args+es.length }

/-- Capacity collection contains no random instruction. -/
theorem capacityCollectEdgesBody_noRand (b : ℕ) : (capacityCollectEdgesBody b).NoRand := by
  simp only [capacityCollectEdgesBody,Stmt.NoRand,and_self]

/-- The scan writes exactly the model's capacity list in the original edge
order, with linear cost and exact fresh allocation. -/
theorem capacityCollectEdges_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (capacityCollectEdgesModule b)) (J : Circulation) (es : List (Fin J.m)) :
    MeetsContract w p b (capacityCollectEdgesContract w J es) := by
  induction es with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,heap,rfl,_,_,_,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+0 < 2^w at hs
    have hh : heap < 2^w := by omega
    apply runs_start_le
    unfold capacityCollectEdgesBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap+0 ∧ (∀ x < heap,mem x = mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap=heap+0
        exact ⟨⟨le_rfl,by omega,fun _ _ => rfl,hz,listAt_nil _ _⟩,by omega⟩
      · simp only [capacityCollectEdgesContract,heapContract,List.length_nil,
          Expr.size_bin,Expr.size_reg,Expr.size_const]; omega
    · simp at hcond
  | cons e es ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,heap,rfl,hat,hend,hvalues,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+(e::es).length < 2^w at hs
    obtain ⟨hhead,htail⟩ := listAt_append.mp hat
    change ListAt mem a (J.solverEdgeWords e) at hhead
    change ListAt mem (a+5) (es.flatMap J.solverEdgeWords) at htail
    have hcap : mem (a+2)=J.capacity e := by
      have h := hhead 2 (by change 2<5; decide)
      simpa only [Circulation.solverEdgeWords,List.getElem_cons_succ,List.getElem_cons_zero] using h
    have hcapWord := hvalues e List.mem_cons_self
    have hh : heap < 2^w := by omega
    have hh1 : heap+1 < 2^w := by simp only [List.length_cons] at hs; omega
    have ha5 : a+5 < 2^w := by simp only [List.length_cons] at hend; omega
    have ha2 : a+2 < 2^w := by omega
    have hlen : (e::es).length < 2^w := hwords _ (by simp)
    have htailLen : es.length < 2^w := by simp only [List.length_cons] at hlen; omega
    let memS := Function.update mem heap (J.capacity e)
    have hframeS : ∀ x < heap,memS x = mem x := by
      intro x hx
      exact Function.update_of_ne (by omega : x≠heap) _ _
    have hzS : ZeroFrom memS (heap+1) := by
      intro x hx
      dsimp only [memS]
      rw [Function.update_of_ne (by omega : x≠heap)]
      exact hz x (by omega)
    have htailS := htail.of_agree_below (h₀ := heap) (by
      rw [J.solverEdgeRecords_length]
      simp only [List.length_cons] at hend
      omega) hframeS
    apply runs_start_le
    unfold capacityCollectEdgesBody
    wram_step
    · simp at hcond
    · refine runs_seq_store_le (x := heap) (v := J.capacity e) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_call_le ih (vs := [a+5,es.length,heap+1]) ?_ (by wram_words) ?_ ?_
      · have heq : (e::es).length-1=es.length := rfl
        rw [← heq]
        eval_expr
      · refine ⟨⟨a+5,heap+1,rfl,htailS,?_,
          (fun e' he' => hvalues e' (List.mem_cons_of_mem e he')),hw⟩,hzS,?_⟩
        · simp only [List.length_cons] at hend
          omega
        · change heap+1+es.length < 2^w
          simp only [List.length_cons] at hs
          omega
      · intro ret memR posR hpostR
        obtain ⟨⟨_,_,hframeR,hzR,hatR⟩,hret⟩ := hpostR
        change ret=heap+1+es.length at hret
        change (∀ x < heap+1,memR x = memS x) at hframeR
        change ZeroFrom memR ret at hzR
        change ListAt memR (heap+1) (es.map J.capacity) at hatR
        have hr : ret < 2^w := by simp only [List.length_cons] at hs; omega
        refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · change (heap ≤ ret ∧ ret ≤ heap+(e::es).length ∧ (∀ x < heap,memR x = mem x) ∧
            ZeroFrom memR ret ∧ ListAt memR heap ((e::es).map J.capacity)) ∧ ret=heap+(e::es).length
          refine ⟨⟨by omega,by simp only [List.length_cons]; omega,?_,hzR,?_⟩,
            by simp only [List.length_cons]; omega⟩
          · intro x hx
            exact (hframeR x (by omega)).trans (hframeS x hx)
          · apply listAt_cons.mpr
            exact ⟨(hframeR heap (by omega)).trans (Function.update_self _ _ _),hatR⟩
        · simp only [capacityCollectEdgesContract,heapContract,List.length_cons,
            argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
          omega

/-- Every selected source record list has simultaneous collection premises
in canonical record memory at a finite width. -/
theorem exists_capacityCollectEdges_pre (J : Circulation) (es : List (Fin J.m)) :
    ∃ w,(∀ x ∈ [0,es.length,5*es.length],x < 2^w) ∧
      (capacityCollectEdgesContract w J es).pre [0,es.length,5*es.length]
        (initMem (es.flatMap J.solverEdgeWords)) := by
  let input := es.flatMap J.solverEdgeWords ++ [6*es.length+10]
  let w := wordSize 1 input
  have hw : 6*es.length+10 < 2^w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_right _ List.mem_cons_self)
  refine ⟨w,?_,⟨0,5*es.length,rfl,listAt_initMem _,by omega,?_,by omega⟩,?_,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · intro e he
    exact lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨e,he,by simp [Circulation.solverEdgeWords]⟩))
  · change ZeroFrom (initMem (es.flatMap J.solverEdgeWords)) (5*es.length)
    simpa only [J.solverEdgeRecords_length] using zeroFrom_initMem (es.flatMap J.solverEdgeWords)
  · change 5*es.length+es.length < 2^w
    omega

end MinCostFlow.Scaling.Machine
