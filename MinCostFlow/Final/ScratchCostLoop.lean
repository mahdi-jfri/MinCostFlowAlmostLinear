module

public import MinCostFlow.Final.ScratchCostRounds
public import MinCostFlow.Scaling.CostLoopContract
import MinCostFlow.Scaling.CostLoopPrefixWords
import MinCostFlow.Scaling.CostLoopWorkLower
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.CirculationLayout
import WordRAM.Tactic

/-!
# The measured cost loop with polynomial scratch

The entry computes the prescribed number of rounds and initializes the
integer state. The verified loop then returns that model's last state.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Round counting, zero-state initialization, and all repeated cost rounds. -/
def scratchCostLoopModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  costLoopBody (b+1) (b+3) (b+5) ::
    (costRoundsModule (b+1) ++ costInitialModule (b+3) ++ scratchCostRoundsLoopModule solver entry (b+5) c d)

/-- Exact complete measured loop, with setup charged to its model work. -/
noncomputable def scratchCostLoopContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C U : ℕ) : Contract :=
  let N := (costStepNumberBase J C U)^(524*scratchWidthFactor c d)
  let fuel := costRounds J.n C
  let r := costLoopMeasured (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U) J C
  { pre := fun args mem => ∃ a heap,args=[a,C,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
      0<J.m ∧ J.n+1≤U ∧ ZeroFrom mem heap ∧ heap+J.m+2*J.n+3+(fuel+1)*N<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧
      ret≤heapArg args+J.m+2*J.n+3+fuel*N ∧ CostStateAt mem' (ret-3) ret r.value ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => r.calls.length*((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n))+
      301000*scratchWorkFactor solver c d*r.work }

/-- Counting, initialization, and repetition are deterministic. -/
theorem scratchCostLoopModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchCostLoopModule solver entry b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [costLoopBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hl
    · rcases List.mem_append.mp hb with hr | hi
      · exact costRoundsModule_noRand _ body hr
      · exact costInitialModule_noRand _ body hi
    · exact scratchCostRoundsLoopModule_noRand solver entry _ c d hdet body hl

set_option exponentiation.threshold 1024 in
private theorem oldReserve {w : ℕ} (J : Circulation) (C U c d heap : ℕ)
    (h : heap+J.m+2*J.n+3+(costRounds J.n C+1)*(costStepNumberBase J C U)^(524*scratchWidthFactor c d)<2^w) :
    heap+J.m+2*J.n+3+(costRounds J.n C+1)*(costStepNumberBase J C U)^524<2^w := by
  have hD : 0<costStepNumberBase J C U := by unfold costStepNumberBase; omega
  have hf := scratchWidthFactor_pos c d
  apply lt_of_le_of_lt _ h
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hD (by omega))) _

private theorem full_cost_loop_padding (ln lc calls Q W reg : ℕ) (hW : 1+lc+ln≤W) :
    0+(1+1)+2+(1+(1+0))+(40*ln+40*lc+100)+2+(1+(1+0))+100+2+
      (1+1+1)+2+(1+(1+(1+(1+(1+(1+0))))))+
      (calls*Q+300000*(reg+1)*W+100)+2+(1+1)≤calls*Q+301000*(reg+1)*W := by
  have hr : W≤(reg+1)*W := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right W (show 1≤reg+1 by omega)
  simp only [Nat.mul_assoc]
  omega

private theorem full_cost_n_eval {w a n : ℕ} {st : State} (h0 : st.regs 0=a) (hn : st.mem a=n) :
    Expr.eval w st (.load (.reg 0))=some n := by eval_expr

private theorem full_cost_round_args {w n C : ℕ} {st : State} (h4 : st.regs 4=n) (h1 : st.regs 1=C) :
    evalArgs w st [.reg 4,.reg 1]=some [n,C] := by eval_expr

private theorem full_cost_initial_args {w a heap : ℕ} {st : State} (h0 : st.regs 0=a) (h3 : st.regs 3=heap) :
    evalArgs w st [.reg 0,.reg 3]=some [a,heap] := by eval_expr

private theorem full_cost_state_eval {w heap : ℕ} {st : State} (h6 : st.regs 6=heap)
    (hh : heap<2^w) (h3 : 3<2^w) : Expr.eval w st (.bin .sub (.reg 6) (.const 3))=some (heap-3) := by eval_expr

private theorem full_cost_loop_args {w a state fuel C U heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h7 : st.regs 7=state) (h5 : st.regs 5=fuel) (h1 : st.regs 1=C)
    (h2 : st.regs 2=U) (h6 : st.regs 6=heap) :
    evalArgs w st [.reg 0,.reg 7,.reg 5,.reg 1,.reg 2,.reg 6]=some [a,state,fuel,C,U,heap] := by eval_expr

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 2048 in
/-- The complete measured cost-loop machine returns exactly the model
state and charges actual primitive calls plus `301000*(regBound+1)*work`,
including all setup and initialization instructions. -/
theorem scratchCostLoop_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (scratchCostLoopModule solver entry b c d)) (J : Circulation) (C U : ℕ) :
    MeetsContract w p b (scratchCostLoopContract w solver entry T S c d hproc J C U) := by
  let inner := fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U
  let N := (costStepNumberBase J C U)^(524*scratchWidthFactor c d)
  let fuel := costRounds J.n C
  let r := costLoopMeasured inner J C
  have ht := hasAt_tail hp
  have hleft := hasAt_append_left ht
  have hRounds := hasAt_append_left hleft
  have hInitial : p.HasAt (b+3) (costInitialModule (b+3)) := by
    simpa only [costRoundsModule,clogTwoModule,List.length_cons,List.length_nil,Nat.add_assoc,Nat.reduceAdd] using hasAt_append_right hleft
  have hLoop : p.HasAt (b+5) (scratchCostRoundsLoopModule solver entry (b+5) c d) := by
    simpa only [costRoundsModule,clogTwoModule,costInitialModule,costHeaderModule,
      List.length_append,List.length_cons,List.length_nil,Nat.add_assoc,Nat.reduceAdd] using hasAt_append_right ht
  have hkR := costRounds_meetsContract (w := w) hRounds J.n C
  have hkI := costInitial_meetsContract (w := w) hInitial J
  have hkL := scratchCostRoundsLoop_meetsContract (w := w) hproc hScratch hdet hmono hLoop J C U fuel
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hC,hu,hm,hnU,hz,hs⟩ := hpre
  have hroundPre := costRounds_pre_of_loop_space J C U heap mem (oldReserve J C U c d heap hs)
  obtain ⟨_,hn2,hC2,hfuel,h2⟩ := hroundPre
  have hD8 : 8≤costStepNumberBase J C U := by dsimp only [costStepNumberBase]; omega
  have hN : 1≤N := Nat.one_le_pow (524*scratchWidthFactor c d) _ (by omega)
  have hspace : heap+J.m+2*J.n+3+(fuel+1)*N<2^w := hs
  have hh : heap<2^w := by omega
  have hCword : C<2^w := by omega
  have hUword : U<2^w := hwords U (by simp)
  have hnWord : J.n<2^w := by omega
  have hMword : J.m<2^w := by omega
  have ha : a<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hNcell := (solver_header_at J hgraph).1
  apply runs_start_le
  unfold costLoopBody
  refine runs_seq_assign_le (v := J.n) (full_cost_n_eval (by rfl) hNcell) ?_
  refine runs_seq_call_le hkR (vs := [J.n,C]) (full_cost_round_args (by rfl) (by rfl)) (by wram_words)
    ⟨rfl,hn2,hC2,hfuel,h2⟩ ?_
  intro count memR posR hpostR
  obtain ⟨hcount,hmemR⟩ := hpostR
  change count=fuel at hcount
  subst count
  change memR=mem at hmemR
  subst memR
  refine runs_seq_call_le hkI (vs := [a,heap]) (full_cost_initial_args (by rfl) (by rfl)) (by wram_words)
    ⟨a,heap,rfl,hgraph,hgraphEnd,hz,by omega⟩ ?_
  intro initHeap memI posI hpostI
  obtain ⟨hinit,hstateI,hzI,hframeI⟩ := hpostI
  change initHeap=heap+J.m+2*J.n+3 at hinit
  change CostStateAt memI (initHeap-3) initHeap (CostState.initial J) at hstateI
  change ZeroFrom memI initHeap at hzI
  change (∀ x<heap,memI x=mem x) at hframeI
  have hinitWord : initHeap<2^w := by omega
  have hstateWord : initHeap-3<2^w := by omega
  have hgraphI := hgraph.of_agree_below hgraphEnd hframeI
  refine runs_seq_assign_le (v := initHeap-3) (full_cost_state_eval (by rfl) hinitWord (by omega)) ?_
  refine runs_seq_call_le hkL (vs := [a,initHeap-3,fuel,C,U,initHeap])
    (full_cost_loop_args (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)) (by wram_words)
    ⟨a,initHeap-3,initHeap,rfl,hgraphI,by omega,by omega,hstateI,hC,hu,hm,hnU,le_rfl,hzI,
      by change initHeap+(fuel+1)*N<2^w; omega⟩ ?_
  intro ret memL posL hpostL
  obtain ⟨hloL,hhiL,hstateL,hzL,hframeL⟩ := hpostL
  change initHeap≤ret at hloL
  change ret≤ initHeap+fuel*N at hhiL
  change (∀ x< initHeap,memL x=memI x) at hframeL
  refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change heap≤ret ∧ ret≤heap+J.m+2*J.n+3+fuel*N ∧ CostStateAt memL (ret-3) ret r.value ∧
      ZeroFrom memL ret ∧ ∀ x<heap,memL x=mem x
    refine ⟨by omega,by omega,hstateL,hzL,?_⟩
    intro x hx
    exact (hframeL x (by omega)).trans (hframeI x hx)
  · have hwork : 1+Nat.clog 2 (C+1)+Nat.clog 2 (J.n+1)≤r.work := costLoopMeasured_rounds_le_work inner J C
    have hpad := full_cost_loop_padding (Nat.clog 2 (J.n+1)) (Nat.clog 2 (C+1)) r.calls.length
      ((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n)) r.work (scratchWorkFactor solver c d - 1) hwork
    simpa only [r,costLoopMeasured,inner,fuel,scratchCostLoopContract,costRoundsContract,costInitialContract,scratchCostRoundsLoopContract,
      startState,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,
      Nat.add_assoc,Nat.reduceAdd,scratchWorkFactor_succ] using hpad

end MinCostFlow.Final
