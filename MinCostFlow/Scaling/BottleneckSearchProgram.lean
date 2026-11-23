module

public import MinCostFlow.Scaling.BottleneckSearchContract
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import Mathlib.Tactic.ClearExclamation

/-!
# Execution of the complete bottleneck search

The preparation produces the model's exact sorted candidates. Initialize
the full half-open interval and run precisely the ceiling-logarithmic
number of rounds. Every stored best flow is the actual canonical solution
retained by the mathematical model, rather than an arbitrary optimum.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem search_cost_padding (m L sortWork calls B loopWork : ℕ) (hL : L≤m+1) :
    0+(1+1+1+1)+2+(1+1+1)+2+(1+0)+(40*L+20)+2+
      (1+(1+0))+(80*m+200*sortWork+40*L+900)+2+(1+1+1)+2+
      (1+(1+(1+(1+(1+(1+0))))))+40+2+(1+(1+(1+(1+(1+0)))))+
      (calls*B+200*loopWork+20)+2+(1+1) ≤
      calls*B+200*(sortWork+loopWork+m)+1500 := by omega

/-- The complete machine entry computes exactly `bottleneckSearch`, with
all solver calls, sorting, setup, and loop work charged explicitly. -/
theorem bottleneckSearch_meetsContract {w b : ℕ} {P solver : Program} {f : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver f (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (J : Circulation) (C : ℕ)
    (hc : J.CostsBounded (J.m^10)) (hC : J.CostsBounded C)
    (hp : P.HasAt b (bottleneckSearchModule solver f b)) :
    MeetsContract w P b (bottleneckSearchContract w solver f T hproc J C) := by
  let log := b+1+(capacityCandidatesModule (b+1)).length
  let writer := log+1
  let loop := writer+1
  have htail := hasAt_tail hp
  have hbeforeLoop := hasAt_append_left htail
  have hbeforeWriter := hasAt_append_left hbeforeLoop
  have hprepare := hasAt_append_left hbeforeWriter
  have hlog : P.HasAt log (clogTwoModule log) := hasAt_append_right hbeforeWriter
  have hwriter : P.HasAt writer wordFiveModule := by
    simpa only [List.length_append,clogTwoModule,List.length_cons,List.length_nil,Nat.add_assoc,writer,log] using
      hasAt_append_right hbeforeLoop
  have hloop : P.HasAt loop (bottleneckLoopModule solver f loop) := by
    simpa only [List.length_append,clogTwoModule,wordFiveModule,List.length_cons,List.length_nil,Nat.add_assoc,loop,writer,log] using
      hasAt_append_right htail
  let solve := canonicalSolver solver f T hproc
  let L := Nat.clog 2 (J.m+1)
  let candidates := (sortCapacities (List.ofFn J.capacity)).1
  let G := bottleneckGuestBound J candidates
  let A := 12+15*J.m+2^G
  let initial : BottleneckState J := ⟨0,J.m,none⟩
  let r := CallResult.forRounds (BottleneckState.step solve candidates) L initial
  have hcandidateLen : candidates.length=J.m := by
    simpa only [List.length_ofFn] using (sortCapacities_perm (List.ofFn J.capacity)).length_eq
  have hL : L≤J.m+1 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hG : 0<2^G := Nat.two_pow_pos G
  have hA : 5≤A := by dsimp only [A]; omega
  have hLA : A≤(L+1)*A := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right A (show 1≤L+1 by omega)
  have hkP := capacityCandidates_meetsContract (w := w) hprepare J
  have hkL := clogTwo_meetsContract (w := w) hlog (J.m+1)
  have hkW := wordFive_meetsContract (w := w) hwriter
  have hkR := bottleneckLoop_meetsContract (w := w) hproc hdet J candidates initial C L hc hC hloop
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,heap,rfl,hgraph,hgraphEnd,hinput,hm2,hbudget,hguest,hw⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(J.m+(L+1)*J.m+5+(L+1)*A)<2^w at hs
  have hh : heap<2^w := by omega
  have hm : J.m<2^w := by omega
  have hm1 : J.m+1<2^w := by omega
  have hLword : L<2^w := by omega
  have hAword : A<2^w := by omega
  have hsmall : 2*J.m+2<2^w := by change 12+15*J.m+2^G<2^w at hAword; omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hM := (solver_header_at J hgraph).2
  have hvalues : ∀ x ∈ candidates,x<2^w := by
    intro x hx
    have hx' := (sortCapacities_perm (List.ofFn J.capacity)).mem_iff.mp hx
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hx'
    exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
  apply runs_start_le
  unfold bottleneckSearchBody
  refine runs_seq_assign_le (v := J.m) (by clear! solver T solve G A r; eval_expr) ?_
  refine runs_seq_assign_le (v := J.m+1) (by clear! solver T solve G A r; eval_expr) ?_
  refine runs_seq_call_le hkL (vs := [J.m+1]) (by clear! solver T solve G A r; eval_expr)
    (by wram_words) ⟨rfl,hm2,by omega⟩ ?_
  intro logValue memL posL hpostL
  obtain ⟨hmemL,hlogValue⟩ := hpostL
  subst memL
  subst logValue
  refine runs_seq_call_le hkP (vs := [a,heap]) (by clear! solver T solve G A r; eval_expr)
    (by wram_words) ?_ ?_
  · exact ⟨⟨a,heap,rfl,hgraph,hgraphEnd,hinput,hm2,hw⟩,hz,
      by change heap+(J.m+(L+1)*J.m)<2^w; omega⟩
  · intro candidateEnd memP posP hpostP
    obtain ⟨⟨hlo,hhi,hframeP,hzP,_⟩,hcandidateLower,harray⟩ := hpostP
    change heap≤candidateEnd at hlo
    change candidateEnd≤heap+(J.m+(L+1)*J.m) at hhi
    change (∀ x<heap,memP x=mem x) at hframeP
    change ZeroFrom memP candidateEnd at hzP
    change heap+J.m≤candidateEnd at hcandidateLower
    change ListAt memP (candidateEnd-J.m) candidates at harray
    have hpWord : candidateEnd<2^w := by omega
    have hvecWord : candidateEnd-J.m<2^w := by omega
    have hgraphP := hgraph.of_agree_below hgraphEnd hframeP
    refine runs_seq_assign_le (v := candidateEnd-J.m) (by clear! solver T solve G A r; eval_expr) ?_
    refine runs_seq_call_le hkW (vs := [0,J.m,0,0,0,candidateEnd]) (by clear! solver T solve G A r; eval_expr)
      (by wram_words) ⟨⟨0,J.m,0,0,0,candidateEnd,rfl⟩,hzP,by change candidateEnd+5<2^w; omega⟩ ?_
    intro startHeap memW posW hpostW
    obtain ⟨⟨_,_,hframeW,hzW,hheader⟩,hstartHeap⟩ := hpostW
    change startHeap=candidateEnd+5 at hstartHeap
    change (∀ x<candidateEnd,memW x=memP x) at hframeW
    change ZeroFrom memW startHeap at hzW
    change ListAt memW candidateEnd [0,J.m,0,0,0] at hheader
    have hstartWord : startHeap<2^w := by omega
    have hstate : BottleneckStateAt memW candidateEnd initial := bottleneckStateAt_of_header_none hheader
    have hgraphW := hgraphP.of_agree_below (hgraphEnd.trans hlo) hframeW
    have harrayW := harray.of_agree_below (h₀ := candidateEnd)
      (by rw [hcandidateLen]; omega) hframeW
    have hheaderWords : ∀ i<5,memW (candidateEnd+i)<2^w := by
      intro i hi
      have hcell := hheader i (by change i<5; exact hi)
      have hi' : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
      rcases hi' with rfl | rfl | rfl | rfl | rfl <;>
        simp only [List.getElem_cons_zero,List.getElem_cons_succ] at hcell <;> rw [hcell] <;> omega
    have hbest : ∀ u flow,initial.best=some (u,flow) → memW (candidateEnd+4)+J.m≤startHeap := by
      intro u flow hf
      cases hf
    refine runs_seq_call_le hkR (vs := [a,candidateEnd-J.m,candidateEnd,L,startHeap])
      (by clear! solver T solve G A r; eval_expr) (by wram_words) ?_ ?_
    · refine ⟨⟨a,candidateEnd-J.m,candidateEnd,startHeap,rfl,?_,by omega,hLword⟩,hzW,?_⟩
      · refine ⟨⟨a,candidateEnd-J.m,candidateEnd,startHeap,rfl,hgraphW,harrayW,hstate,
          hgraphEnd.trans (by omega),?_,by omega,hinput,hvalues,hheaderWords,hbest,
          hcandidateLen,Nat.zero_le _,le_rfl,hsmall,hbudget,hguest,hw⟩,hzW,?_⟩
        · rw [hcandidateLen]; omega
        · change startHeap+(if 0<J.m then A else 5)<2^w
          split <;> omega
      · change startHeap+(L+1)*A<2^w
        omega
    · intro ret memR posR hpostR
      obtain ⟨⟨hloR,hhiR,hframeR,hzR,_⟩,_,hstateR,hheaderR,hbestR⟩ := hpostR
      change startHeap≤ret at hloR
      change ret≤startHeap+(L+1)*A at hhiR
      change (∀ x<startHeap,memR x=memW x) at hframeR
      change ZeroFrom memR ret at hzR
      change BottleneckStateAt memR (ret-5) r.value at hstateR
      change (∀ i<5,memR (ret-5+i)<2^w) at hheaderR
      change (∀ u flow,r.value.best=some (u,flow) → memR (ret-5+4)+J.m≤ret) at hbestR
      have hr : ret<2^w := by omega
      refine runs_ret_le (v := ret) (by clear! solver T solve G A r; eval_expr) ?_ ?_
      · change (heap≤ret ∧ ret≤heap+(J.m+(L+1)*J.m+5+(L+1)*A) ∧
          (∀ x<heap,memR x=mem x) ∧ ZeroFrom memR ret ∧ True) ∧ heap+5≤ret ∧
          BottleneckStateAt memR (ret-5) (bottleneckSearch solve J).value ∧
          (∀ i<5,memR (ret-5+i)<2^w) ∧ _
        refine ⟨⟨by omega,by omega,?_,hzR,True.intro⟩,by omega,hstateR,hheaderR,hbestR⟩
        intro x hx
        exact (hframeR x (by omega)).trans ((hframeW x (by omega)).trans (hframeP x hx))
      · simp only [bottleneckSearchContract,capacityCandidatesContract,clogTwoContract,wordFiveContract,
          bottleneckLoopContract,heapContract,bottleneckSearch,argsSize_cons,argsSize_nil,
          Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        have hcost := search_cost_padding J.m L (sortCapacities (List.ofFn J.capacity)).2 r.calls.length
          ((solver.regBound+6)*T (J.n+1) J.m+40*G+solver.regBound) r.work hL
        simpa only [Nat.add_assoc,Nat.reduceAdd] using hcost

end MinCostFlow.Scaling.Machine
