module

public import MinCostFlow.Scaling.CycleInitialLayout
public import MinCostFlow.Scaling.BuildAdjacencyProgram
public import MinCostFlow.Scaling.IndexRangeProgram
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.CirculationLayout
import WordRAM.Tactic

/-!
# Initializing the exact cycle extraction state

Reserve the zero header and path flags, construct positive-flow adjacency,
and prepend the ordered edge-index range to an empty candidate list.
One header store installs the range pointer. The resulting state is exactly
`cycleInitial`, with linear cost and fresh allocation.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,flow,stateHeap]`. -/
def cycleInitialBody (adjacency range : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 5 (.bin .add (.bin .add (.reg 2) (.const 9)) (.reg 3)) ;;
  .call 6 adjacency [.reg 0,.reg 1,.reg 5] ;;
  .call 7 range [.reg 4,.const 0,.reg 6] ;;
  .store (.bin .add (.reg 2) (.const 2))
    (.bin .mul (.bin .lt (.const 0) (.reg 4)) (.bin .sub (.reg 7) (.const 2))) ;;
  .ret (.reg 7)

/-- Initialization entry, adjacency construction, and ordered candidate nodes. -/
def cycleInitialModule (b : ℕ) : List Stmt :=
  let range := b+1+(buildAdjacencyModule (b+1)).length
  cycleInitialBody (b+1) range :: (buildAdjacencyModule (b+1) ++ indexRangeModule range)

/-- Input graph and unsigned nonnegative flow precede fresh state storage. -/
def cycleInitialContract (w : ℕ) (J : Circulation) (flow : Fin J.m → ℤ) : Contract where
  pre args mem := ∃ a flowPtr base,args=[a,flowPtr,base] ∧
    ListAt mem a J.solverWords ∧ ListAt mem flowPtr (List.ofFn (fun e => (flow e).toNat)) ∧
    a+J.solverWords.length≤base ∧ flowPtr+J.m≤base ∧
    (∀ e,0≤flow e ∧ (flow e).toNat<2^w) ∧ ZeroFrom mem base ∧
    base+10+3*J.n+4*J.m<2^w ∧ 9<2^w
  post args mem ret mem' := cycleNodes J.n (heapArg args)≤ret ∧
    ret≤cycleNodes J.n (heapArg args)+4*J.m ∧
    CycleStateAt mem' (heapArg args) ret (J.cycleInitial flow) ∧
    ZeroFrom mem' ret ∧ (∀ x<heapArg args,mem' x=mem x) ∧
    ∀ i<9,mem' (heapArg args+i)<2^w
  cost _ _ := 400*J.m+500

/-- Initialization and its callees have no random instruction. -/
theorem cycleInitialModule_noRand (b : ℕ) : ∀ body ∈ cycleInitialModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [cycleInitialBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with ha | hr
    · exact buildAdjacencyModule_noRand _ body ha
    · exact indexRangeModule_noRand _ body hr

private theorem cycle_initial_ptr_eval {w : ℕ} {st : State} {count heap : ℕ}
    (hc : st.regs 4=count) (hh : st.regs 7=heap)
    (_hcWord : count<2^w) (hhWord : heap<2^w) (htwo : 2<2^w) :
    Expr.eval w st (.bin .mul (.bin .lt (.const 0) (.reg 4))
      (.bin .sub (.reg 7) (.const 2)))=some (if count=0 then 0 else heap-2) := by
  have heq : (if 0<count then 1 else 0)*(heap-2)=(if count=0 then 0 else heap-2) := by
    by_cases hz : count=0
    · simp only [hz,Nat.lt_irrefl,↓reduceIte,Nat.zero_mul]
    · simp only [Nat.pos_of_ne_zero hz,hz,↓reduceIte,Nat.one_mul]
  have hp : (if 0<count then 1 else 0)*(heap-2)<2^w := by rw [heq]; split <;> omega
  have h := Expr.eval_mul
    (Expr.eval_lt_op (x := 0) (y := count) (by eval_expr) (by eval_expr) (by omega))
    (Expr.eval_sub (x := heap) (y := 2) (by eval_expr) (by eval_expr) hhWord) hp
  simpa only [heq] using h

/-- The machine initializer constructs exactly the model's cycle state,
including the original-order candidate list, with linear cost and space. -/
theorem cycleInitial_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (cycleInitialModule b)) (J : Circulation) (flow : Fin J.m → ℤ) :
    MeetsContract w p b (cycleInitialContract w J flow) := by
  have hkA := buildAdjacency_meetsContract (w := w) (hasAt_append_left (hasAt_tail hp)) J flow
  have hrange := hasAt_append_right (hasAt_tail hp)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,flowPtr,base,rfl,hgraph,hflow,hgraphEnd,hflowEnd,hvalues,hz,hs,hw⟩ := hpre
  let heads := cycleHeads J.n base
  let nodes := cycleNodes J.n base
  have hN := (solver_header_at J hgraph).1
  have hM := (solver_header_at J hgraph).2
  have hn : J.n<2^w := by omega
  have hm : J.m<2^w := by omega
  have ha : a<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hf : flowPtr<2^w := by omega
  have hb : base<2^w := by omega
  have hb9 : base+9<2^w := by omega
  have hb2 : base+2<2^w := by omega
  have hheads : heads<2^w := by dsimp only [heads,cycleHeads]; omega
  have hnodes : nodes=base+10+3*J.n := rfl
  have hkR := indexRange_meetsContract (w := w) (lo := nodes) (m := J.m) hrange J.m []
  apply runs_start_le
  unfold cycleInitialBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heads) (by dsimp only [heads,cycleHeads]; eval_expr) ?_
  refine runs_seq_call_le hkA (vs := [a,flowPtr,heads]) (by eval_expr) (by wram_words) ?_ ?_
  · refine ⟨a,flowPtr,heads,rfl,hgraph,hflow,?_,?_,hvalues,?_,?_,by omega⟩
    · dsimp only [heads,cycleHeads]; omega
    · dsimp only [heads,cycleHeads]; omega
    · intro x hx
      exact hz x (by dsimp only [heads,cycleHeads] at hx; omega)
    · dsimp only [heads,cycleHeads]; omega
  · intro adjEnd memA posA hpostA
    obtain ⟨hlo,hhi,hout,hzA,hframeA⟩ := hpostA
    change heads+2*J.n+1≤adjEnd at hlo
    change adjEnd≤heads+2*J.n+1+2*J.m at hhi
    change AdjacencyAt memA heads (heads+2*J.n+1) adjEnd (J.buildAdjacency flow) at hout
    change ZeroFrom memA adjEnd at hzA
    change (∀ x<heads,memA x=mem x) at hframeA
    have hnodeEq : heads+2*J.n+1=nodes := by dsimp only [heads,nodes,cycleHeads,cycleNodes]; omega
    rw [hnodeEq] at hlo hhi hout
    have haWord : adjEnd<2^w := by dsimp only [nodes,cycleNodes] at hhi; omega
    have hpositive : 0<adjEnd := by dsimp only [nodes,cycleNodes] at hlo; omega
    refine runs_seq_call_le hkR (vs := [J.m,0,adjEnd]) (by eval_expr) (by wram_words)
      ⟨⟨0,adjEnd,rfl,le_rfl,hpositive,hlo,.nil,by omega⟩,hzA,
        by change adjEnd+2*J.m<2^w; dsimp only [nodes,cycleNodes] at hhi; omega⟩ ?_
    intro ret memR posR hpostR
    obtain ⟨⟨_,_,hframeR,hzR,hcandidates⟩,hret⟩ := hpostR
    change ret=adjEnd+2*J.m at hret
    change (∀ x<adjEnd,memR x=memA x) at hframeR
    change ZeroFrom memR ret at hzR
    change IndexListAt memR nodes (adjEnd+2*J.m)
      (if J.m=0 then 0 else adjEnd+2*J.m-2) ((List.finRange J.m).take J.m++[]) at hcandidates
    let ptr := if J.m=0 then 0 else ret-2
    have hcan : IndexListAt memR nodes ret ptr (List.finRange J.m) := by
      have htake : (List.finRange J.m).take J.m=List.finRange J.m :=
        List.take_of_length_le (Nat.le_of_eq List.length_finRange)
      simpa only [←hret,htake,List.append_nil] using hcandidates
    have hr : ret<2^w := by dsimp only [nodes,cycleNodes] at hhi; omega
    have hpword : ptr<2^w := by dsimp only [ptr]; split <;> omega
    have houtR := hout.of_agree_below (by dsimp only [heads,nodes,cycleHeads,cycleNodes]; omega)
      (show adjEnd≤ret by omega) hframeR
    have hzeroPrefix : ∀ x,base≤x → x<heads → memR x=0 := by
      intro x hx hxend
      rw [hframeR x (by dsimp only [heads,nodes,cycleHeads,cycleNodes] at *; omega),hframeA x hxend]
      exact hz x hx
    let memS := Function.update memR (base+2) ptr
    have hstate : CycleStateAt memS base ret (J.cycleInitial flow) :=
      cycleStateAt_initial_of_parts J flow hzeroPrefix houtR hcan
    have hzS : ZeroFrom memS ret := by
      intro x hx
      dsimp only [memS]
      rw [Function.update_of_ne (by dsimp only [nodes,cycleNodes] at hlo; omega)]
      exact hzR x hx
    refine runs_seq_store_le (x := base+2) (v := ptr) (by eval_expr) ?_ ?_
    · exact cycle_initial_ptr_eval (by rfl) (by rfl) hm hr (by omega)
    · refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · change nodes≤ret ∧ ret≤nodes+4*J.m ∧ CycleStateAt memS base ret (J.cycleInitial flow) ∧
          ZeroFrom memS ret ∧ (∀ x<base,memS x=mem x) ∧ ∀ i<9,memS (base+i)<2^w
        refine ⟨by omega,by omega,hstate,hzS,?_,?_⟩
        · intro x hx
          dsimp only [memS]
          rw [Function.update_of_ne (by omega : x≠base+2),hframeR x (by dsimp only [nodes,cycleNodes] at hlo; omega),
            hframeA x (by dsimp only [heads,cycleHeads]; omega)]
        · intro i hi
          by_cases heq : i=2
          · subst i
            simpa only [memS,Function.update_self] using hpword
          · dsimp only [memS]
            rw [Function.update_of_ne (by omega),hzeroPrefix _ (by omega)
              (by dsimp only [heads,cycleHeads]; omega)]
            exact Nat.two_pow_pos w
      · simp only [cycleInitialContract,buildAdjacencyContract,indexRangeContract,heapContract,
          argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        omega

end MinCostFlow.Scaling.Machine
