module

public import MinCostFlow.Final.ScratchBottleneckLoop
public import MinCostFlow.Scaling.BottleneckSearchContract
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.CirculationLayout
import WordRAM.Tactic
import Mathlib.Tactic.ClearExclamation

/-!
# The bottleneck search with polynomial scratch

The program sorts the capacities, forms the initial interval, and
executes the ceiling-logarithmic number of search rounds. Its bound
counts the guest solver calls that the search actually makes.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Preparation, ceiling logarithm, initial header, and bounded search. -/
def scratchBottleneckSearchModule (solver : Program) (f b c d : ℕ) : List Stmt :=
  let log := b+1+(capacityCandidatesModule (b+1)).length
  let writer := log+1
  let loop := writer+1
  bottleneckSearchBody (b+1) log writer loop ::
    (capacityCandidatesModule (b+1) ++ clogTwoModule log ++ wordFiveModule ++ scratchBottleneckLoopModule solver f loop c d)

/-- Exact search output and counted model cost. The space reserve covers
candidate sorting, an initial header, and every possible threshold guest. -/
noncomputable def scratchBottleneckSearchContract (w : ℕ) (solver : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C : ℕ) : Contract :=
  let L := Nat.clog 2 (J.m+1)
  let candidates := (sortCapacities (List.ofFn J.capacity)).1
  let G := scratchBottleneckGuestBound c d J candidates
  let A := 12+15*J.m+2^G
  let result := bottleneckSearch ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)) J
  let H := heapContract w
    (fun args mem => ∃ a heap,args=[a,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length ≤ heap ∧ (∀ x ∈ J.solverWords,x<2^w) ∧
      J.m+2<2^w ∧ J.m*C<2^w ∧ 2^(G+1)+2≤2^w ∧ 8<2^w)
    (fun _ _ _ => True)
    (fun _ _ => result.calls.length*
      ((solver.regBound+6)*T (J.n+1) J.m+40*G+solver.regBound)+200*result.work+1500)
    (fun _ _ => J.m+(L+1)*J.m+5+(L+1)*A)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧
      heapArg args+5≤ret ∧ BottleneckStateAt mem' (ret-5) result.value ∧
      (∀ i<5,mem' (ret-5+i)<2^w) ∧
      (∀ u flow,result.value.best=some (u,flow) → mem' (ret-5+4)+J.m≤ret) }

/-- The entire search contains no random instruction when its solver is deterministic. -/
theorem scratchBottleneckSearchModule_noRand (solver : Program) (f b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchBottleneckSearchModule solver f b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [bottleneckSearchBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hl
    · rcases List.mem_append.mp hb with hb | hw
      · rcases List.mem_append.mp hb with hc | hg
        · exact capacityCandidatesModule_noRand _ body hc
        · have he : body=clogTwoBody (b+1+(capacityCandidatesModule (b+1)).length) := by
            simpa only [clogTwoModule,List.mem_singleton] using hg
          subst body
          exact clogTwoBody_noRand _
      · have he : body=wordFiveBody := by simpa only [wordFiveModule,List.mem_singleton] using hw
        subst body
        exact wordFiveBody_noRand
    · exact scratchBottleneckLoopModule_noRand solver f _ c d hdet body hl

/-- The complete search uses at most a ceiling-logarithmic number of
solver calls and linear-logarithmic model work. -/
theorem scratchBottleneckSearch_cost_le (w : ℕ) (solver : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C : ℕ) (args : List ℕ) (mem : ℕ → ℕ) :
    (scratchBottleneckSearchContract w solver f T S c d hproc J C).cost args mem ≤
      Nat.clog 2 (J.m+1)*((solver.regBound+6)*T (J.n+1) J.m+
        40*scratchBottleneckGuestBound c d J (sortCapacities (List.ofFn J.capacity)).1+solver.regBound)+
      24000*(Nat.clog 2 (J.m+1)+1)*(J.m+1)+1500 := by
  have hc := bottleneckSearch_calls ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)) J
  have hw := bottleneckSearch_work ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)) J
  let B := (solver.regBound+6)*T (J.n+1) J.m+
    40*scratchBottleneckGuestBound c d J (sortCapacities (List.ofFn J.capacity)).1+solver.regBound
  change (bottleneckSearch ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)) J).calls.length*B+
    200*(bottleneckSearch ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)) J).work+1500 ≤ _
  have hc' := Nat.mul_le_mul_right B hc
  have hw' := Nat.mul_le_mul_left 200 hw
  have hbound := Nat.add_le_add_right (Nat.add_le_add hc' hw') 1500
  simpa only [←Nat.mul_assoc] using hbound

private theorem search_cost_padding (m L sortWork calls B loopWork : ℕ) (hL : L≤m+1) :
    0+(1+1+1+1)+2+(1+1+1)+2+(1+0)+(40*L+20)+2+
      (1+(1+0))+(80*m+200*sortWork+40*L+900)+2+(1+1+1)+2+
      (1+(1+(1+(1+(1+(1+0))))))+40+2+(1+(1+(1+(1+(1+0)))))+
      (calls*B+200*loopWork+20)+2+(1+1) ≤
      calls*B+200*(sortWork+loopWork+m)+1500 := by omega

/-- The complete machine entry computes exactly `bottleneckSearch`, with
all solver calls, sorting, setup, and loop work charged explicitly. -/
theorem scratchBottleneckSearch_meetsContract {w b : ℕ} {P solver : Program} {f : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hdet : solver.IsDeterministic) (J : Circulation) (hnGraph : J.n ≤ 2*J.m) (C : ℕ)
    (hc : J.CostsBounded (J.m^10)) (hC : J.CostsBounded C)
    (hS : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hp : P.HasAt b (scratchBottleneckSearchModule solver f b c d)) :
    MeetsContract w P b (scratchBottleneckSearchContract w solver f T S c d hproc J C) := by
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
  have hloop : P.HasAt loop (scratchBottleneckLoopModule solver f loop c d) := by
    simpa only [List.length_append,clogTwoModule,wordFiveModule,List.length_cons,List.length_nil,Nat.add_assoc,loop,writer,log] using
      hasAt_append_right htail
  let solve := (fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)
  let L := Nat.clog 2 (J.m+1)
  let candidates := (sortCapacities (List.ofFn J.capacity)).1
  let G := scratchBottleneckGuestBound c d J candidates
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
  have hkR := scratchBottleneckLoop_meetsContract (w := w) hproc hdet J hnGraph candidates initial C L hc hC hS hloop
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
      · simp only [scratchBottleneckSearchContract,capacityCandidatesContract,clogTwoContract,wordFiveContract,
          scratchBottleneckLoopContract,heapContract,bottleneckSearch,argsSize_cons,argsSize_nil,
          Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        have hcost := search_cost_padding J.m L (sortCapacities (List.ofFn J.capacity)).2 r.calls.length
          ((solver.regBound+6)*T (J.n+1) J.m+40*G+solver.regBound) r.work hL
        simpa only [Nat.add_assoc,Nat.reduceAdd] using hcost

end MinCostFlow.Final
