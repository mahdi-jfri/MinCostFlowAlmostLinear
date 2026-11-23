module

public import MinCostFlow.Final.ScratchBottleneckTest
public import MinCostFlow.Scaling.BottleneckStepContract
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.CirculationLayout
import WordRAM.Tactic
import Mathlib.Tactic.ClearExclamation

/-!
# A bottleneck search step with polynomial scratch

The step tests the midpoint of a nonempty interval. It uses the
largest guest width in the candidate list to reserve space for the
test and the next state. An empty interval needs only a state copy.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Maximum canonical guest width among the stored threshold candidates. -/
def scratchBottleneckGuestBound (c d : ℕ) (J : Circulation) (candidates : List ℕ) : ℕ :=
  (candidates.map (fun u => wordSize (scratchWordMultiplier c d) (J.bottleneckGraph u).positiveInstance.solverWords)).foldr max 0

/-- Every candidate's guest width is at most the common search bound. -/
theorem scratchBottleneckGuest_le (c d : ℕ) (J : Circulation) {candidates : List ℕ} {u : ℕ}
    (hu : u ∈ candidates) :
    wordSize (scratchWordMultiplier c d) (J.bottleneckGraph u).positiveInstance.solverWords ≤ scratchBottleneckGuestBound c d J candidates :=
  Link.elem_le_foldr_max (List.mem_map.mpr ⟨u,hu,rfl⟩)

/-- One test's complete fresh allocation is bounded uniformly over the
candidate list. Five further words suffice for its new search header. -/
theorem scratchBottleneckTest_space_le (c d : ℕ) (J : Circulation) {candidates : List ℕ} {u : ℕ}
    (hu : u ∈ candidates) :
    7+15*J.m+2^(wordSize (scratchWordMultiplier c d) (J.bottleneckGraph u).positiveInstance.solverWords)+5 ≤
      12+15*J.m+2^(scratchBottleneckGuestBound c d J candidates) := by
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (scratchBottleneckGuest_le c d J hu)
  omega

/-- Uniform cost of a test, in the solver dimensions of the original
circulation, with only linear edge work and the canonical width overhead. -/
theorem scratchBottleneckTest_cost_le (w : ℕ) (solver : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) {candidates : List ℕ} {u : ℕ} (hu : u ∈ candidates)
    (C : ℕ) (args : List ℕ) (mem : ℕ → ℕ) :
    (scratchBottleneckTestContract w solver f T S c d hproc J u C).cost args mem ≤
      (solver.regBound+6)*T (J.n+1) J.m+40*scratchBottleneckGuestBound c d J candidates+
        solver.regBound+1500*J.m+1760 := by
  have hwidth := scratchBottleneckGuest_le c d J hu
  change (solver.regBound+6)*T (J.n+1) J.m+
    80*(J.bottleneckGraph u).positiveInstance.solverWords.length+
      40*wordSize (scratchWordMultiplier c d) (J.bottleneckGraph u).positiveInstance.solverWords+solver.regBound+1100*J.m+1600 ≤ _
  rw [Circulation.solverWords_length]
  change (solver.regBound+6)*T (J.n+1) J.m+
    80*(2+5*J.m)+40*wordSize (scratchWordMultiplier c d) (J.bottleneckGraph u).positiveInstance.solverWords+
      solver.regBound+1100*J.m+1600 ≤ _
  omega

/-- Step entry followed by its exact test and fresh state update. -/
def scratchBottleneckStepModule (solver : Program) (f b c d : ℕ) : List Stmt :=
  let u := b+1+(scratchBottleneckTestModule solver f (b+1) c d).length
  bottleneckStepBody (b+1) u ::
    (scratchBottleneckTestModule solver f (b+1) c d ++ bottleneckUpdateModule u)

/-- Exact model state update, with common candidate workspace and a solver
cost only when the interval is nonempty. Header and referenced-flow bounds
are preserved for the next iteration. -/
noncomputable def scratchBottleneckStepContract (w : ℕ) (solver : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (candidates : List ℕ) (s : BottleneckState J) (C : ℕ) : Contract :=
  let G := scratchBottleneckGuestBound c d J candidates
  let next := (BottleneckState.step ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)) candidates s).value
  let H := heapContract w
    (fun args mem => ∃ a vec state heap,args=[a,vec,state,heap] ∧
      ListAt mem a J.solverWords ∧ ListAt mem vec candidates ∧ BottleneckStateAt mem state s ∧
      a+J.solverWords.length ≤ heap ∧ vec+candidates.length ≤ heap ∧ state+5 ≤ heap ∧
      (∀ x ∈ J.solverWords,x<2^w) ∧ (∀ x ∈ candidates,x<2^w) ∧
      (∀ i<5,mem (state+i)<2^w) ∧
      (∀ u flow,s.best=some (u,flow) → mem (state+4)+J.m ≤ heap) ∧
      candidates.length=J.m ∧ s.lower≤s.upper ∧ s.upper≤J.m ∧
      2*J.m+2<2^w ∧ J.m*C<2^w ∧ 2^(G+1)+2 ≤ 2^w ∧ 8<2^w)
    (fun _ _ _ => True)
    (fun _ _ => if s.lower<s.upper then
      (solver.regBound+6)*T (J.n+1) J.m+40*G+solver.regBound+1500*J.m+2200 else 200)
    (fun _ _ => if s.lower<s.upper then 12+15*J.m+2^G else 5)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧
      heapArg args+5 ≤ ret ∧ BottleneckStateAt mem' (ret-5) next ∧
      (∀ i<5,mem' (ret-5+i)<2^w) ∧
      (∀ u flow,next.best=some (u,flow) → mem' (ret-5+4)+J.m ≤ ret) }

/-- The step is deterministic whenever the supplied solver is. -/
theorem scratchBottleneckStepModule_noRand (solver : Program) (f b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchBottleneckStepModule solver f b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [bottleneckStepBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with ht | hu
    · exact scratchBottleneckTestModule_noRand solver f _ c d hdet body ht
    · exact bottleneckUpdateModule_noRand _ body hu

/-- The step's machine cost charges the canonical solver overhead exactly
once per recorded model call. All remaining instructions are covered by a
constant multiple of the model's non-solver work. -/
theorem scratchBottleneckStep_cost_model_le (w : ℕ) (solver : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (candidates : List ℕ) (s : BottleneckState J) (C : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    (scratchBottleneckStepContract w solver f T S c d hproc J candidates s C).cost args mem ≤
      (BottleneckState.step ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)) candidates s).calls.length*
        ((solver.regBound+6)*T (J.n+1) J.m+40*scratchBottleneckGuestBound c d J candidates+solver.regBound)+
      200*(BottleneckState.step ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)) candidates s).work := by
  by_cases ha : s.lower<s.upper
  · simp only [scratchBottleneckStepContract,heapContract,BottleneckState.step,ha,↓reduceIte,
      List.length_cons,List.length_nil]
    omega
  · simp only [scratchBottleneckStepContract,heapContract,BottleneckState.step,ha,↓reduceIte,
      List.length_nil,Nat.zero_mul,Nat.mul_one,Nat.zero_add]
    exact le_rfl

private theorem step_sign_eval {w : ℕ} {st : State} {heap sign : ℕ}
    (hr : st.regs 9=heap) (hm : st.mem (heap-2)=sign)
    (hh : heap<2^w) (ht : 2<2^w) (_hs : sign<2^w) :
    Expr.eval w st (.load (.bin .sub (.reg 9) (.const 2)))=some sign := by
  eval_expr

private theorem step_cost_padding (x y : ℕ) (h : x≤y) :
    0+(1+1+1+1)+2+(1+1)+2+(1+1+1+1)+2+(1+1+1)+1+(1+1+1+1+1)+2+
      (1+1+1+1)+2+(1+(1+(1+0)))+x+2+(1+(1+1+1+1+1)+1)+2+(1+1+1+1)+2+
      (1+(1+(1+(1+(1+(1+0))))))+140+2+(1+1)≤y+440 := by omega

/-- A machine step computes exactly `BottleneckState.step`, preserving the
representation and word bounds for a subsequent iteration. -/
theorem scratchBottleneckStep_meetsContract {w b : ℕ} {P solver : Program} {f : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hdet : solver.IsDeterministic) (J : Circulation) (hnGraph : J.n ≤ 2*J.m) (candidates : List ℕ)
    (s : BottleneckState J) (C : ℕ) (hc : J.CostsBounded (J.m^10)) (hC : J.CostsBounded C)
    (hS : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hp : P.HasAt b (scratchBottleneckStepModule solver f b c d)) :
    MeetsContract w P b (scratchBottleneckStepContract w solver f T S c d hproc J candidates s C) := by
  have htest := hasAt_append_left (hasAt_tail hp)
  have hupdate := hasAt_append_right (hasAt_tail hp)
  let G := scratchBottleneckGuestBound c d J candidates
  let solve := (fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,vec,state,heap,rfl,hgraph,hvec,hstate,hgraphEnd,hvecEnd,hstateEnd,
    hinput,hvalues,hheader,hbestBound,hlen,hlower,hupper,hsmall,hbudget,hguest,hw⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change 2^(G+1)+2≤2^w at hguest
  have hG0 : 0<2^G := Nat.two_pow_pos G
  change heap+(if s.lower<s.upper then 12+15*J.m+2^G else 5)<2^w at hs
  have hh : heap<2^w := by omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hst : state<2^w := by omega
  have hst1 : state+1<2^w := by omega
  have hm : J.m<2^w := by omega
  have hlowWord : s.lower<2^w := by omega
  have huWord : s.upper<2^w := by omega
  have hu1 : s.upper+1<2^w := by omega
  have hzWord : 0<2^w := by omega
  have hM := (solver_header_at J hgraph).2
  have hL := hstate.1
  have hU := hstate.2.1
  apply runs_start_le
  unfold bottleneckStepBody
  refine runs_seq_assign_le (v := J.m) (by clear! solver T G solve; eval_expr) ?_
  refine runs_seq_assign_le (v := s.lower) (by clear! solver T G solve; eval_expr) ?_
  refine runs_seq_assign_le (v := s.upper) (by clear! solver T G solve; eval_expr) ?_
  wram_step
  · have ha : s.lower<s.upper := hcond
    have hsA : heap+(12+15*J.m+2^G)<2^w := by simpa only [ha,↓reduceIte] using hs
    let mid := (s.lower+s.upper)/2
    let u := candidates.getD mid 0
    let K := J.bottleneckGraph u
    let delta := Circulation.solveWithZeroCapacities solve K
    let objective := K.integerObjective delta
    let g := wordSize (scratchWordMultiplier c d) K.positiveInstance.solverWords
    have hmid := bottleneck_mid_bounds ha hupper
    have hmidLen : mid<candidates.length := by dsimp only [mid]; omega
    have huMem : u ∈ candidates := by
      dsimp only [u]
      rw [List.getD_eq_getElem _ _ hmidLen]
      exact List.getElem_mem hmidLen
    have hcandidate : mem (vec+mid)=u := by
      dsimp only [u]
      rw [List.getD_eq_getElem _ _ hmidLen]
      exact hvec mid hmidLen
    have huFit : u<2^w := hvalues u huMem
    have hmidFit : mid<2^w := by dsimp only [mid]; omega
    have hmid1 : mid+1<2^w := by dsimp only [mid]; omega
    have hsum : s.lower+s.upper<2^w := by omega
    have hindex : vec+mid<2^w := by omega
    have hg0 : 0<2^g := Nat.two_pow_pos g
    have hguestLe : g≤G := scratchBottleneckGuest_le c d J huMem
    have hpow : 2^g≤2^G := Nat.pow_le_pow_right (by decide) hguestLe
    have hmargin : 2^(g+1)+2≤2^w := by
      have h := Nat.pow_le_pow_right (by decide : 0<2) (Nat.add_le_add_right hguestLe 1)
      omega
    have hkT := scratchBottleneckTest_meetsContract (w := w) hproc hdet J hnGraph u C hc hC hS htest
    have hkU := bottleneckUpdate_meetsContract (w := w) hupdate s mid u delta objective
    have hopt : K.Optimal (fun e => (delta e : ℝ)) := by
      apply Circulation.solveWithZeroCapacities_of_optimal
      exact compressedCanonicalSolverAt_optimal _ solver f T S (hproc K.positiveInstance) K.positiveInstance
    have hnonneg : ∀ e,0≤delta e := fun e => Int.cast_nonneg_iff.mp (hopt.1.2 e).1
    refine runs_seq_assign_le (v := mid) (by clear! solver T G solve K delta objective g; eval_expr) ?_
    refine runs_seq_assign_le (v := u) (by clear! solver T G solve K delta objective g; eval_expr) ?_
    refine runs_seq_call_le hkT (vs := [a,u,heap]) (by clear! solver T G solve K delta objective g; eval_expr)
      (by wram_words) ?_ ?_
    · exact ⟨⟨a,heap,rfl,hgraph,hgraphEnd,hinput,hbudget,hmargin,hw⟩,hz,
        by change heap+(7+15*J.m+2^g)<2^w; omega⟩
    · intro testEnd memT posT hpostT
      obtain ⟨⟨_,_,hframeT,hzT,_⟩,htestEnd,hflow,hobjective⟩ := hpostT
      change testEnd=heap+7+15*J.m+2^g at htestEnd
      change (∀ x<heap,memT x=mem x) at hframeT
      change ZeroFrom memT testEnd at hzT
      change ListAt memT (testEnd-(5*J.m+2)) (List.ofFn (fun e => (delta e).toNat)) at hflow
      change ListAt memT (testEnd-2) (encodeInt objective) at hobjective
      have htword : testEnd<2^w := by omega
      have hflowWord : testEnd-(5*J.m+2)<2^w := by omega
      have hmulWord : 5*J.m<2^w := by omega
      have hoffWord : 5*J.m+2<2^w := by omega
      have hsignPtr : testEnd-2<2^w := by omega
      have hsigncell : memT (testEnd-2)=(if objective<0 then 1 else 0) := (listAt_cons.mp hobjective).1
      have hsignWord : (if objective<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
      have hread : J.readSolverFlow memT (testEnd-(5*J.m+2))=delta := solverOutput_read_eq J hnonneg hflow
      have hstateT := hstate.of_agree_below hstateEnd hbestBound hframeT
      have hheaderT : ∀ i<5,memT (state+i)<2^w := by
        intro i hi
        rw [hframeT (state+i) (by omega)]
        exact hheader i hi
      have hbestBoundT : ∀ u f,s.best=some (u,f) → memT (state+4)+J.m≤testEnd := by
        intro u f hf
        rw [hframeT (state+4) (by omega)]
        exact (hbestBound u f hf).trans (by omega)
      refine runs_seq_assign_le (v := testEnd-(5*J.m+2)) (by clear! solver T G solve K delta objective g; eval_expr) ?_
      refine runs_seq_assign_le (v := if objective<0 then 1 else 0) (step_sign_eval (by rfl) hsigncell htword (by omega) hsignWord) ?_
      refine runs_seq_call_le hkU (vs := [state,mid,u,testEnd-(5*J.m+2),if objective<0 then 1 else 0,testEnd])
        (by clear! solver T G solve K delta g; eval_expr) (by wram_words) ?_ ?_
      · refine ⟨⟨state,testEnd-(5*J.m+2),testEnd,rfl,hstateT,by omega,by omega,hread,hmid1,
          hheaderT,hbestBoundT⟩,hzT,?_⟩
        change testEnd+5<2^w
        omega
      · intro ret memR posR hpostR
        obtain ⟨⟨_,_,hframeR,hzR,_⟩,hret,hstateR,hheaderR,hbestR⟩ := hpostR
        change ret=testEnd+5 at hret
        change (∀ x<testEnd,memR x=memT x) at hframeR
        change ZeroFrom memR ret at hzR
        have hr : ret<2^w := by omega
        have hnext := bottleneckStep_value_active solve candidates s ha
        change (BottleneckState.step solve candidates s).value=
          (if objective<0 then ⟨mid+1,s.upper,some (u,delta)⟩ else {s with upper:=mid}) at hnext
        refine runs_ret_le (v := ret) (by clear! solver T G solve K delta objective g; eval_expr) ?_ ?_
        · change (heap≤ret ∧ ret≤heap+(if s.lower<s.upper then 12+15*J.m+2^G else 5) ∧
            (∀ x<heap,memR x=mem x) ∧ ZeroFrom memR ret ∧ True) ∧ heap+5≤ret ∧
            BottleneckStateAt memR (ret-5) (BottleneckState.step solve candidates s).value ∧
            (∀ i<5,memR (ret-5+i)<2^w) ∧ _
          refine ⟨⟨by omega,by simp only [ha,↓reduceIte]; omega,?_,hzR,True.intro⟩,by omega,?_,hheaderR,?_⟩
          · intro x hx
            exact (hframeR x (by omega)).trans (hframeT x hx)
          · rw [hnext]; exact hstateR
          · rw [hnext]; exact hbestR
        · have hcost := scratchBottleneckTest_cost_le w solver f T S c d hproc J huMem C [a,u,heap] mem
          simp only [scratchBottleneckStepContract,scratchBottleneckTestContract,bottleneckUpdateContract,heapContract,ha,↓reduceIte,
            argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_reg,Expr.size_const,Expr.size_load]
          dsimp only [scratchBottleneckTestContract,heapContract] at hcost
          simpa only [Nat.add_assoc,Nat.reduceAdd] using step_cost_padding _ _ hcost
  · have ha : ¬s.lower<s.upper := hcond
    have hsI : heap+5<2^w := by simpa only [ha,↓reduceIte] using hs
    have hkU := bottleneckUpdate_meetsContract (w := w) hupdate s s.upper 0 (J.readSolverFlow mem 0) 0
    have hdim : J.m≤heap := by rw [J.solverWords_length] at hgraphEnd; omega
    refine runs_seq_call_le hkU (vs := [state,s.upper,0,0,0,heap]) (by clear! solver T G solve; eval_expr)
      (by wram_words) ?_ ?_
    · exact ⟨⟨state,0,heap,rfl,hstate,hstateEnd,by omega,rfl,hu1,hheader,hbestBound⟩,hz,hsI⟩
    · intro ret memR posR hpostR
      obtain ⟨⟨_,_,hframeR,hzR,_⟩,hret,hstateR,hheaderR,hbestR⟩ := hpostR
      change ret=heap+5 at hret
      change (∀ x<heap,memR x=mem x) at hframeR
      change ZeroFrom memR ret at hzR
      have hr : ret<2^w := by omega
      have hnext := bottleneckStep_value_inactive solve candidates s ha
      simp only [Int.lt_irrefl,↓reduceIte] at hstateR hbestR
      refine runs_ret_le (v := ret) (by clear! solver T G solve; eval_expr) ?_ ?_
      · change (heap≤ret ∧ ret≤heap+(if s.lower<s.upper then 12+15*J.m+2^G else 5) ∧
          (∀ x<heap,memR x=mem x) ∧ ZeroFrom memR ret ∧ True) ∧ heap+5≤ret ∧
          BottleneckStateAt memR (ret-5) (BottleneckState.step solve candidates s).value ∧
          (∀ i<5,memR (ret-5+i)<2^w) ∧ _
        refine ⟨⟨by omega,by simp only [ha,↓reduceIte]; omega,hframeR,hzR,True.intro⟩,by omega,?_,hheaderR,?_⟩
        · rw [hnext]; exact hstateR
        · rw [hnext]; exact hbestR
      · simp only [scratchBottleneckStepContract,bottleneckUpdateContract,heapContract,ha,↓reduceIte,
          argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_reg,Expr.size_const,Expr.size_load]
        omega

end MinCostFlow.Final
