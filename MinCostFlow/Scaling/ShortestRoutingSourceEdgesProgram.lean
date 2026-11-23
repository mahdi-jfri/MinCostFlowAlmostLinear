module

public import MinCostFlow.Scaling.ShortestRoutingLayout
public import MinCostFlow.Scaling.WordFiveProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# The added source arcs of the shortest-routing graph

Enumerate the old vertices in order. Each output record has source `n`,
that vertex as its head, capacity `n+1`, and zero cost. The scan writes the
source block in the common five-word circulation layout.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[count,firstVertex,vertexCount,heap]`. -/
def shortestRoutingSourceEdgesBody (self writer : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 0) (.const 0)) (.ret (.reg 3))
    (.call 4 writer [.reg 2,.reg 1,.bin .add (.reg 2) (.const 1),.const 0,.const 0,.reg 3] ;;
     .call 5 self [.bin .sub (.reg 0) (.const 1),.bin .add (.reg 1) (.const 1),.reg 2,.reg 4] ;;
     .ret (.reg 5))

/-- The source-arc scan and five-word writer. -/
def shortestRoutingSourceEdgesModule (b : ℕ) : List Stmt :=
  shortestRoutingSourceEdgesBody b (b+1) :: wordFiveModule

/-- The selected vertices are consecutive and stay within the old vertex set. -/
def shortestRoutingSourceEdgesContract (w : ℕ) (J : Circulation) (vs : List (Fin J.n)) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ first heap, args = [vs.length,first,J.n,heap] ∧
      (∀ i : Fin vs.length, (vs[i.val]).val = first+i.val) ∧
      first+vs.length ≤ J.n ∧ J.n+1 < 2^w ∧ 8 < 2^w)
    (fun args _ mem' => ListAt mem' (heapArg args)
      (vs.flatMap (fun v => J.shortestRoutingGraph.solverEdgeWords (Fin.natAdd J.m v))))
    (fun _ _ => 150*vs.length+20) (fun _ _ => 5*vs.length)
  { C with post := fun args mem ret mem' => C.post args mem ret mem' ∧ ret = heapArg args+5*vs.length }

/-- Source-arc construction has no random instruction. -/
theorem shortestRoutingSourceEdgesModule_noRand (b : ℕ) :
    ∀ body ∈ shortestRoutingSourceEdgesModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [shortestRoutingSourceEdgesBody,Stmt.NoRand,and_self]
  · have he : body = wordFiveBody := by simpa only [wordFiveModule,List.mem_singleton] using hb
    subst body
    exact wordFiveBody_noRand

/-- The scan writes exactly the selected consecutive source arcs with
linear cost and five fresh words per arc. -/
theorem shortestRoutingSourceEdges_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (shortestRoutingSourceEdgesModule b)) (J : Circulation) (vs : List (Fin J.n)) :
    MeetsContract w p b (shortestRoutingSourceEdgesContract w J vs) := by
  have hkW := wordFive_meetsContract (w := w) (hasAt_tail hp)
  induction vs with
  | nil =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨first,heap,rfl,_,_,_,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+5*0 < 2^w at hs
    have hh : heap < 2^w := by omega
    apply runs_start_le
    unfold shortestRoutingSourceEdgesBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap+5*0 ∧ (∀ x < heap,mem x = mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap = heap+5*0
        exact ⟨⟨le_rfl,by omega,fun _ _ => rfl,hz,listAt_nil _ _⟩,by omega⟩
      · simp only [shortestRoutingSourceEdgesContract,heapContract,List.length_nil,
          Expr.size_bin,Expr.size_reg,Expr.size_const]; omega
    · simp at hcond
  | cons v vs ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨first,heap,rfl,hconsecutive,hend,hn1,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+5*(v::vs).length < 2^w at hs
    have hv : v.val = first := by
      have h := hconsecutive ⟨0,by simp only [List.length_cons]; omega⟩
      simpa only [List.getElem_cons_zero,Nat.add_zero] using h
    have htail : ∀ i : Fin vs.length, (vs[i.val]).val = (first+1)+i.val := by
      intro i
      have h := hconsecutive ⟨i.val+1,by simp only [List.length_cons]; omega⟩
      simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have hh : heap < 2^w := by omega
    have hh5 : heap+5 < 2^w := by simp only [List.length_cons] at hs; omega
    have hn : J.n < 2^w := by omega
    have hfirst : first < 2^w := by simp only [List.length_cons] at hend; omega
    have hfirst1 : first+1 < 2^w := by simp only [List.length_cons] at hend; omega
    have hlen := hwords (v::vs).length List.mem_cons_self
    have htailLen : vs.length < 2^w := by simp only [List.length_cons] at hlen; omega
    apply runs_start_le
    unfold shortestRoutingSourceEdgesBody
    wram_step
    · simp at hcond
    · refine runs_seq_call_le hkW (vs := [J.n,first,J.n+1,0,0,heap]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨_,_,_,_,_,heap,rfl⟩,hz,hh5⟩
      · intro next memW posW hpostW
        obtain ⟨⟨_,_,hframeW,hzW,hatW⟩,hnext⟩ := hpostW
        change next = heap+5 at hnext
        change (∀ x < heap,memW x = mem x) at hframeW
        change ZeroFrom memW next at hzW
        change ListAt memW heap [J.n,first,J.n+1,0,0] at hatW
        have hnextWord : next < 2^w := by omega
        refine runs_seq_call_le ih (vs := [vs.length,first+1,J.n,next]) ?_ (by wram_words) ?_ ?_
        · have heq : (v::vs).length-1 = vs.length := rfl
          rw [← heq]
          eval_expr
        · refine ⟨⟨first+1,next,rfl,htail,?_,hn1,hw⟩,hzW,?_⟩
          · simp only [List.length_cons] at hend
            omega
          · change next+5*vs.length < 2^w
            simp only [List.length_cons] at hs
            omega
        · intro ret memR posR hpostR
          obtain ⟨⟨_,_,hframeR,hzR,hatR⟩,hret⟩ := hpostR
          change ret = next+5*vs.length at hret
          change (∀ x < next,memR x = memW x) at hframeR
          change ZeroFrom memR ret at hzR
          change ListAt memR next (vs.flatMap (fun v => J.shortestRoutingGraph.solverEdgeWords (Fin.natAdd J.m v))) at hatR
          have hr : ret < 2^w := by simp only [List.length_cons] at hs; omega
          refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
          · change (heap ≤ ret ∧ ret ≤ heap+5*(v::vs).length ∧ (∀ x < heap,memR x = mem x) ∧
              ZeroFrom memR ret ∧ ListAt memR heap
                ((v::vs).flatMap (fun v => J.shortestRoutingGraph.solverEdgeWords (Fin.natAdd J.m v)))) ∧
              ret = heap+5*(v::vs).length
            refine ⟨⟨by omega,by simp only [List.length_cons]; omega,?_,hzR,?_⟩,
              by simp only [List.length_cons]; omega⟩
            · intro x hx
              exact (hframeR x (by omega)).trans (hframeW x hx)
            · rw [List.flatMap_cons]
              apply listAt_append.mpr
              refine ⟨?_,?_⟩
              · rw [shortestRouting_source_edgeWords,hv]
                exact hatW.of_agree_below (by change heap+5 ≤ next; omega) hframeR
              · simpa only [Circulation.solverEdgeWords,List.length_cons,List.length_nil,
                  Nat.reduceAdd,hnext] using hatR
          · simp only [shortestRoutingSourceEdgesContract,heapContract,wordFiveContract,
              List.length_cons,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_reg,Expr.size_const]; omega

/-- Every graph has simultaneous source-block premises for the full old
vertex list in fresh zero memory. -/
theorem exists_shortestRoutingSourceEdges_pre (J : Circulation) :
    ∃ w, (∀ x ∈ [J.n,0,J.n,0],x < 2^w) ∧
      (shortestRoutingSourceEdgesContract w J (List.finRange J.n)).pre
        [J.n,0,J.n,0] (fun _ => 0) := by
  let w := 6*J.n+10
  have hw : 6*J.n+10 < 2^w := Nat.lt_two_pow_self
  refine ⟨w,?_,⟨0,0,?_,?_,?_,by omega,by omega⟩,(fun _ _ => rfl),?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · simp only [List.length_finRange]
  · intro i
    simp only [List.getElem_finRange,Nat.zero_add,Fin.val_cast]
  · simp only [List.length_finRange,Nat.zero_add]
    exact le_rfl
  · change 0+5*(List.finRange J.n).length < 2^w
    simp only [List.length_finRange]
    omega

end MinCostFlow.Scaling.Machine
