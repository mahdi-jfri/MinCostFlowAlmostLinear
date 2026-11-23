module

public import MinCostFlow.Final.ScratchCapacityRounds
public import MinCostFlow.Scaling.CapacityLoopContract
import MinCostFlow.Scaling.CapacityLoopPrefixWords
import MinCostFlow.Scaling.CapacityLoopWorkLower
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# The capacity loop with polynomial scratch

The entry computes the round count and initializes the zero flow.
The repeated solver calls use the widened uniform reserve, and the
loop's work counter pays for setup as well as the steps.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- The round-count, zero-flow initialization, and loop follow the entry. -/
def scratchCapacityLoopModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  capacityLoopBody (b+1) (b+3) (b+5) ::
    (capacityRoundsModule (b+1) ++ capacityInitialModule (b+3) ++ scratchCapacityRoundsLoopModule solver entry (b+5) c d)

/-- Exact full capacity loop with all setup charged to its own model work. -/
noncomputable def scratchCapacityLoopContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C U : ℕ) : Contract :=
  let N := (capacityStepNumberBase J C U)^(scratchCapacityExponent c d)
  let fuel := capacityRounds J.m U
  let r := capacityLoop ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J U
  { pre := fun args mem => ∃ a heap,args=[a,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
      0<J.m ∧ ZeroFrom mem heap ∧ heap+J.m+2+(fuel+1)*N<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+J.m+2+fuel*N ∧
      CapacityStateAt mem' (ret-2) ret r.value ∧ ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => r.calls.length*((solver.regBound+6)*T (J.n+1) (J.m+J.m))+
      101000*scratchWorkFactor solver c d*r.work }

/-- Every full-loop procedure is deterministic when the primitive solver is. -/
theorem scratchCapacityLoopModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchCapacityLoopModule solver entry b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityLoopBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hl
    · rcases List.mem_append.mp hb with hr | hi
      · exact capacityRoundsModule_noRand _ body hr
      · exact capacityInitialModule_noRand _ body hi
    · exact scratchCapacityRoundsLoopModule_noRand solver entry _ c d hdet body hl

private theorem full_loop_cost_padding (lm lu calls Q W reg : ℕ) (hW : 1+11*lm+lu≤W) :
    0+(1+(1+1+1))+2+(1+(1+0))+(40*lm+40*lu+100)+2+
      (1+(1+0))+60+2+(1+1+1)+2+(1+(1+(1+(1+0))))+
      (calls*Q+100000*(reg+1)*W+100)+2+(1+1)≤calls*Q+101000*(reg+1)*W := by
  have hr : W≤(reg+1)*W := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right W (show 1≤reg+1 by omega)
  simp only [Nat.mul_assoc]
  omega

private theorem loop_edge_count_eval {w a m : ℕ} {st : State} (h0 : st.regs 0=a)
    (ha : a+1<2^w) (hm : st.mem (a+1)=m) :
    Expr.eval w st (.load (.bin .add (.reg 0) (.const 1)))=some m := by eval_expr

private theorem loop_round_args {w m U : ℕ} {st : State} (h3 : st.regs 3=m) (h1 : st.regs 1=U) :
    evalArgs w st [.reg 3,.reg 1]=some [m,U] := by eval_expr

private theorem loop_initial_args {w a heap : ℕ} {st : State} (h0 : st.regs 0=a) (h2 : st.regs 2=heap) :
    evalArgs w st [.reg 0,.reg 2]=some [a,heap] := by eval_expr

private theorem loop_state_eval {w heap : ℕ} {st : State} (h5 : st.regs 5=heap)
    (hh : heap<2^w) (h2 : 2<2^w) : Expr.eval w st (.bin .sub (.reg 5) (.const 2))=some (heap-2) := by eval_expr

private theorem loop_rounds_args {w a state fuel heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h6 : st.regs 6=state) (h4 : st.regs 4=fuel) (h5 : st.regs 5=heap) :
    evalArgs w st [.reg 0,.reg 6,.reg 4,.reg 5]=some [a,state,fuel,heap] := by eval_expr

/-- The full capacity machine loop computes exactly the model state,
with its actual solver-call term and `101000*(regBound+1)*work` cost. -/
theorem scratchCapacityLoop_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hS : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (scratchCapacityLoopModule solver entry b c d))
    (J : Circulation) (C U : ℕ) (hn : J.n≤2*J.m) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (scratchCapacityLoopContract w solver entry T S c d hproc J C U) := by
  let solve := (fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)
  let N := (capacityStepNumberBase J C U)^(scratchCapacityExponent c d)
  let fuel := capacityRounds J.m U
  let r := capacityLoop solve J U
  have ht := hasAt_tail hp
  have hl := hasAt_append_left ht
  have hRounds := hasAt_append_left hl
  have hInitial : p.HasAt (b+3) (capacityInitialModule (b+3)) := by
    simpa only [capacityRoundsModule,clogTwoModule,List.length_cons,List.length_nil,Nat.add_assoc] using hasAt_append_right hl
  have hLoop : p.HasAt (b+5) (scratchCapacityRoundsLoopModule solver entry (b+5) c d) := by
    simpa only [capacityRoundsModule,clogTwoModule,capacityInitialModule,wordPairModule,
      List.length_append,List.length_cons,List.length_nil,Nat.add_assoc] using hasAt_append_right ht
  have hkR := capacityRounds_meetsContract (w := w) hRounds J.m U
  have hkI := capacityInitial_meetsContract (w := w) hInitial J
  have hkL := scratchCapacityRoundsLoop_meetsContract (w := w) hproc hS hdet hLoop J (CapacityState.initial J) C U fuel hn hc
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hC,hu,hm,hz,hspace⟩ := hpre
  have hroundPre := capacityRounds_pre_of_loop_space J C U heap mem (by
    have hD : 0 < capacityStepNumberBase J C U := by unfold capacityStepNumberBase; omega
    have hf := scratchWidthFactor_pos c d
    have he : 256 ≤ scratchCapacityExponent c d := by unfold scratchCapacityExponent; omega
    apply lt_of_le_of_lt _ hspace
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hD he)) _)
  obtain ⟨_,hm2,hU2,hfuelWord,h11⟩ := hroundPre
  have hD4 : 4≤capacityStepNumberBase J C U := by dsimp only [capacityStepNumberBase]; omega
  have hN : 1≤N := Nat.one_le_pow (scratchCapacityExponent c d) _ (by omega)
  have hspaceNum : heap+J.m+2+(fuel+1)*N<2^w := hspace
  have hh : heap<2^w := by omega
  have hU : U<2^w := by omega
  have hmWord : J.m<2^w := by omega
  have ha : a<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hM := (solver_header_at J hgraph).2
  apply runs_start_le
  unfold capacityLoopBody
  refine runs_seq_assign_le (v := J.m) (loop_edge_count_eval (by rfl) ha1 hM) ?_
  refine runs_seq_call_le hkR (vs := [J.m,U]) (loop_round_args (by rfl) (by rfl)) (by wram_words)
    ⟨rfl,hm2,hU2,hfuelWord,h11⟩ ?_
  intro count memR posR hpostR
  obtain ⟨hcount,hmemR⟩ := hpostR
  change count=fuel at hcount
  subst count
  change memR=mem at hmemR
  subst memR
  refine runs_seq_call_le hkI (vs := [a,heap]) (loop_initial_args (by rfl) (by rfl)) (by wram_words)
    ⟨a,heap,rfl,hgraph,hgraphEnd,hz,by omega,by omega⟩ ?_
  intro initHeap memI posI hpostI
  obtain ⟨hinit,hstateI,hzI,hframeI⟩ := hpostI
  change initHeap=heap+J.m+2 at hinit
  change CapacityStateAt memI (initHeap-2) initHeap (CapacityState.initial J) at hstateI
  change ZeroFrom memI initHeap at hzI
  change (∀ x<heap,memI x=mem x) at hframeI
  have hinitWord : initHeap<2^w := by omega
  have hstateWord : initHeap-2<2^w := by omega
  have hgraphI : ListAt memI a J.solverWords := hgraph.of_agree_below (h₀ := heap) hgraphEnd hframeI
  refine runs_seq_assign_le (v := initHeap-2) (loop_state_eval (by rfl) hinitWord (by omega)) ?_
  refine runs_seq_call_le hkL (vs := [a,initHeap-2,fuel,initHeap])
    (loop_rounds_args (by rfl) (by rfl) (by rfl) (by rfl)) (by wram_words)
    ⟨a,initHeap-2,initHeap,rfl,hgraphI,by omega,by omega,hstateI,
      (fun e => ⟨le_rfl,Int.natCast_nonneg _⟩),hC,hu,hm,hzI,by change initHeap+(fuel+1)*N<2^w; omega,hfuelWord⟩ ?_
  intro ret memL posL hpostL
  obtain ⟨hlo,hhi,hstateL,hzL,hframeL⟩ := hpostL
  change initHeap≤ret at hlo
  change ret≤ initHeap+fuel*N at hhi
  change (∀ x< initHeap,memL x=memI x) at hframeL
  refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change heap≤ret ∧ ret≤heap+J.m+2+fuel*N ∧ CapacityStateAt memL (ret-2) ret r.value ∧
      ZeroFrom memL ret ∧ ∀ x<heap,memL x=mem x
    refine ⟨by omega,by omega,hstateL,hzL,?_⟩
    intro x hx
    exact (hframeL x (by omega)).trans (hframeI x hx)
  · have hwork : 1+11*Nat.clog 2 (J.m+1)+Nat.clog 2 (U+1)≤r.work := capacityLoop_rounds_le_work solve J U
    have hpad := full_loop_cost_padding (Nat.clog 2 (J.m+1)) (Nat.clog 2 (U+1)) r.calls.length
      ((solver.regBound+6)*T (J.n+1) (J.m+J.m)) r.work (scratchWorkFactor solver c d - 1) hwork
    simpa only [r,capacityLoop,solve,fuel,scratchCapacityLoopContract,capacityRoundsContract,capacityInitialContract,scratchCapacityRoundsLoopContract,
      startState,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,
      Nat.add_assoc,Nat.reduceAdd,scratchWorkFactor_succ] using hpad

end MinCostFlow.Final
