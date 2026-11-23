module

public import MinCostFlow.Scaling.ShortestRoutingGraphProgram
public import MinCostFlow.Scaling.ShortestRoutingStartProgram
public import MinCostFlow.Scaling.ResidualProgram
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.CirculationLayout
import WordRAM.Tactic

/-!
# Preparing the residual circulation for shortest-routing optimization

Construct the shortest-routing graph and its direct starting flow, then
construct their residual circulation. Keep the graph and starting vector
in memory for the later augmentation and label traversal. All three
constructions use the common circulation and unsigned-flow layouts.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,heap]`. -/
def routingResidualBody (graph start residual : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 4 (.bin .add (.reg 2) (.reg 3)) ;;
  .call 5 graph [.reg 0,.reg 1] ;;
  .call 6 start [.reg 0,.reg 5] ;;
  .call 7 residual [.reg 1,.reg 5,.reg 6] ;;
  .ret (.reg 7)

/-- Preparation entry and the three constituent constructors. -/
def routingResidualModule (b : ℕ) : List Stmt :=
  routingResidualBody (b+1) (b+7) (b+9) ::
    (shortestRoutingGraphModule (b+1) ++ shortestRoutingStartModule (b+7) ++ residualModule (b+9))

/-- The prepared routing graph, direct starting flow, and residual graph
occupy consecutive regions, with exact address formulas. -/
def routingResidualContract (w : ℕ) (J : Circulation) : Contract :=
  let M := J.m+J.n
  let C := heapContract w
    (fun args mem => ∃ a heap, args = [a,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length ≤ heap ∧ (∀ x ∈ J.solverWords,x < 2^w) ∧
      J.n+1 < 2^w ∧ M < 2^w ∧ 8 < 2^w)
    (fun args _ mem' =>
      ListAt mem' (heapArg args) J.shortestRoutingGraph.solverWords ∧
      ListAt mem' (heapArg args+2+5*M) (List.ofFn (fun e => (J.shortestRoutingStart e).toNat)) ∧
      ListAt mem' (heapArg args+2+6*M)
        (J.shortestRoutingGraph.residual J.shortestRoutingStart).solverWords)
    (fun _ _ => 1000*M+1200) (fun _ _ => 4+16*M)
  { C with post := fun args mem ret mem' => C.post args mem ret mem' ∧ ret = heapArg args+4+16*M }

/-- Every preparation procedure has no random instruction. -/
theorem routingResidualModule_noRand (b : ℕ) : ∀ body ∈ routingResidualModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [routingResidualBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact shortestRoutingGraphModule_noRand _ body hb
      · exact shortestRoutingStartModule_noRand _ body hb
    · exact residualModule_noRand _ body hb

/-- The three constructors compute the exact model routing residual,
preserving the two arrays needed after its optimization. -/
theorem routingResidual_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (routingResidualModule b)) (J : Circulation) :
    MeetsContract w p b (routingResidualContract w J) := by
  have htail := hasAt_tail hp
  have hleft := hasAt_append_left htail
  have hgraph := hasAt_append_left hleft
  have hstart : p.HasAt (b+7) (shortestRoutingStartModule (b+7)) := by
    have h := hasAt_append_right hleft
    have hl : (shortestRoutingGraphModule (b+1)).length = 6 := rfl
    simpa only [hl,Nat.add_assoc] using h
  have hresidual : p.HasAt (b+9) (residualModule (b+9)) := by
    have h := hasAt_append_right htail
    have hl : (shortestRoutingGraphModule (b+1) ++ shortestRoutingStartModule (b+7)).length = 8 := rfl
    simpa only [hl,Nat.add_assoc] using h
  let S := J.shortestRoutingGraph
  let start := J.shortestRoutingStart
  let M := J.m+J.n
  have hslen : S.solverWords.length = 2+5*M := S.solverWords_length
  have hstartBounds : ∀ e,0 ≤ start e ∧ start e ≤ (S.capacity e : ℤ) := by
    intro e
    have h := J.shortestRoutingStart_bounds e
    refine ⟨Int.cast_nonneg_iff.mp h.1,?_⟩
    have hh : (start e : ℝ) ≤ ((S.capacity e : ℤ) : ℝ) := by
      simpa only [Int.cast_natCast] using h.2
    exact Int.cast_le.mp hh
  have hkG := shortestRoutingGraph_meetsContract (w := w) hgraph J
  have hkS := shortestRoutingStart_meetsContract (w := w) hstart J
  have hkR := residual_meetsContract (w := w) hresidual S start
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,heap,rfl,hat,hend,hinput,hn1,hmn,hw⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(4+16*M) < 2^w at hs
  have hn : J.n < 2^w := by omega
  have hm : J.m < 2^w := by dsimp only [M] at hs; omega
  have hsum : J.n+J.m < 2^w := by dsimp only [M] at hs; omega
  have hh : heap < 2^w := by omega
  have haWord := hwords a List.mem_cons_self
  have ha1 : a+1 < 2^w := by rw [J.solverWords_length] at hend; omega
  have hheader := solver_header_at J hat
  obtain ⟨hN,hM⟩ := hheader
  have hSinput := shortestRouting_words_fit J w hinput hn1 hmn
  apply runs_start_le
  unfold routingResidualBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.n+J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkG (vs := [a,heap]) (by eval_expr) hwords ?_ ?_
  · exact ⟨⟨a,heap,rfl,hat,hend,hinput,hn1,hmn,hw⟩,hz,by change heap+(2+5*M) < 2^w; omega⟩
  · intro startPtr memG posG hpostG
    obtain ⟨⟨_,_,hframeG,hzG,hatG⟩,hstartPtr⟩ := hpostG
    change startPtr = heap+2+5*M at hstartPtr
    change (∀ x < heap,memG x = mem x) at hframeG
    change ZeroFrom memG startPtr at hzG
    change ListAt memG heap S.solverWords at hatG
    have hstartWord : startPtr < 2^w := by omega
    have hatOld : ListAt memG a J.solverWords :=
      hat.of_agree_below hend hframeG
    refine runs_seq_call_le hkS (vs := [a,startPtr]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨a,startPtr,rfl,hatOld,by omega,hw⟩,hzG,by change startPtr+M < 2^w; omega⟩
    · intro residualPtr memS posS hpostS
      obtain ⟨⟨_,_,hframeS,hzS,hatStart⟩,hresidualPtr⟩ := hpostS
      change residualPtr = startPtr+J.m+J.n at hresidualPtr
      change (∀ x < startPtr,memS x = memG x) at hframeS
      change ZeroFrom memS residualPtr at hzS
      change ListAt memS startPtr (List.ofFn (fun e => (start e).toNat)) at hatStart
      have hresidualWord : residualPtr < 2^w := by dsimp only [M] at *; omega
      have hatS : ListAt memS heap S.solverWords :=
        hatG.of_agree_below (by rw [hslen]; omega) hframeS
      refine runs_seq_call_le hkR (vs := [heap,startPtr,residualPtr]) (by eval_expr) (by wram_words) ?_ ?_
      · refine ⟨⟨heap,startPtr,residualPtr,rfl,hatS,hatStart,?_,?_,hstartBounds,hSinput,hw⟩,hzS,?_⟩
        · rw [hslen]
          dsimp only [M] at *
          omega
        · change startPtr+M ≤ residualPtr
          dsimp only [M] at *
          omega
        · change residualPtr+(2+10*M) < 2^w
          dsimp only [M] at *
          omega
      · intro ret memR posR hpostR
        obtain ⟨⟨_,_,hframeR,hzR,hatR⟩,hret⟩ := hpostR
        change ret = residualPtr+2+10*M at hret
        change (∀ x < residualPtr,memR x = memS x) at hframeR
        change ZeroFrom memR ret at hzR
        change ListAt memR residualPtr (S.residual start).solverWords at hatR
        have hr : ret < 2^w := by dsimp only [M] at *; omega
        refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · change (heap ≤ ret ∧ ret ≤ heap+(4+16*M) ∧ (∀ x < heap,memR x = mem x) ∧
            ZeroFrom memR ret ∧ ListAt memR heap S.solverWords ∧
            ListAt memR (heap+2+5*M) (List.ofFn (fun e => (start e).toNat)) ∧
            ListAt memR (heap+2+6*M) (S.residual start).solverWords) ∧ ret = heap+4+16*M
          have haddr : residualPtr = heap+2+6*M := by dsimp only [M] at *; omega
          refine ⟨⟨by omega,by omega,?_,hzR,?_,?_,by simpa only [haddr] using hatR⟩,by omega⟩
          · intro x hx
            exact (hframeR x (by omega)).trans ((hframeS x (by omega)).trans (hframeG x hx))
          · exact hatS.of_agree_below (by rw [hslen]; omega) hframeR
          · have hbound : startPtr+M ≤ residualPtr := by dsimp only [M] at *; omega
            have h := hatStart.of_agree_below (by simpa only [List.length_ofFn] using hbound) hframeR
            simpa only [hstartPtr] using h
        · simp only [routingResidualContract,shortestRoutingGraphContract,shortestRoutingStartContract,
            residualContract,heapContract,argsSize_cons,argsSize_nil,Expr.size_bin,
            Expr.size_load,Expr.size_reg,Expr.size_const]
          change _ ≤ 1000*M+1200
          have hsm : S.m = M := rfl
          omega

end MinCostFlow.Scaling.Machine
