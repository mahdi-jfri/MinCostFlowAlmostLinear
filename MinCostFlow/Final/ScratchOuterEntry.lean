module

public import MinCostFlow.Final.ScratchArbitraryDemand
public import MinCostFlow.Scaling.OuterEntryContract
public import MinCostFlow.Final.ScratchInputWidth
import MinCostFlow.Scaling.ArbitraryDemandInputWordSize
import MinCostFlow.Scaling.ArbitraryDemandProgram
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.ScalingSourceWidth
import WordRAM.Entry
import WordRAM.Tactic

/-!
# The original-input entry with polynomial scratch

The entry reads the exact input bounds, runs arbitrary-demand scaling,
and copies the model answer into the required output layout.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- The original input reserves eight times the phase word multiplier. -/
def scratchOuterMultiplier (c d : ℕ) : ℕ := 8*scratchPhaseMultiplier c d

/-- The original scratch policy recovers the original input word size. -/
theorem scratchOuterMultiplier_original : scratchOuterMultiplier 1 4 = 131072 := by
  decide

/-- At multiplier 131072 on exactly `I.encode`, the original maxima and
canonical memory satisfy every arbitrary-demand entry premise jointly. -/
theorem scratchArbitraryDemand_pre_input_wordSize (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (I : Instance) (hv : I.IsValid) :
    (∀ x∈[0,I.maxCost,I.maxCapacity,I.encode.length],x<2^wordSize (scratchOuterMultiplier c d) I.encode) ∧
      (scratchArbitraryDemandContract (wordSize (scratchOuterMultiplier c d) I.encode) solver entry T S c d hproc I hv I.maxCost I.maxCapacity).pre
        [0,I.maxCost,I.maxCapacity,I.encode.length] (initMem I.encode) := by
  let region := 2^wordSize (scratchPhaseMultiplier c d) (I.encode++[max I.maxCost 1,(I.m+1)*I.maxCapacity])
  let w := wordSize (scratchOuterMultiplier c d) I.encode
  have hs := scratch_input_space_wordSize (scratchPhaseMultiplier c d) (scratchPhaseMultiplier_pos c d) I hv
  change I.encode.length+2+10*region<2^w at hs
  have hC : max I.maxCost 1<region := lt_two_pow_wordSize_of_mem (scratchPhaseMultiplier_pos c d)
    (List.mem_append_right _ List.mem_cons_self)
  have hU : (I.m+1)*I.maxCapacity<region := lt_two_pow_wordSize_of_mem (scratchPhaseMultiplier_pos c d)
    (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hUle : I.maxCapacity≤(I.m+1)*I.maxCapacity := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right I.maxCapacity (show 1≤I.m+1 by omega)
  have hCraw : I.maxCost<region := (le_max_left _ _).trans_lt hC
  have hUraw : I.maxCapacity<region := hUle.trans_lt hU
  change (∀ x∈[0,I.maxCost,I.maxCapacity,I.encode.length],x<2^w) ∧
    (scratchArbitraryDemandContract w solver entry T S c d hproc I hv I.maxCost I.maxCapacity).pre
      [0,I.maxCost,I.maxCapacity,I.encode.length] (initMem I.encode)
  refine ⟨?_,0,I.encode.length,rfl,listAt_initMem _,by omega,?_,?_,?_,zeroFrom_initMem _,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega
  · intro e
    exact Link.elem_le_foldr_max (List.mem_map.mpr ⟨I.edge e,List.getElem_mem e.isLt,rfl⟩)
  · intro e
    exact lower_natAbs_le_maxCapacity I _ (List.getElem_mem e.isLt)
  · intro e
    exact upper_natAbs_le_maxCapacity I _ (List.getElem_mem e.isLt)
  · change I.encode.length+10*region<2^w
    omega

/-- The original-input entry, its bound scans, arbitrary-demand scaling,
and final copy procedure occupy consecutive slots. -/
def scratchOuterEntryModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  let solve := b+1+(inputBoundsModule (b+1)).length
  let copy := solve+(scratchArbitraryDemandModule solver entry solve c d).length
  outerEntryBody (b+1) solve copy ::
    (inputBoundsModule (b+1) ++ (scratchArbitraryDemandModule solver entry solve c d ++ [copyWords]))

/-- The whole program starts at procedure zero and has no input-dependent code. -/
def scratchOuterScalingProgram (solver : Program) (entry c d : ℕ) : Program :=
  Program.mk (scratchOuterEntryModule solver entry 0 c d)

/-- The exact model answer is copied to zero, with explicit linear entry
overhead in addition to the complete arbitrary-demand machine budget. -/
noncomputable def scratchOuterEntryContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (I : Instance) (hv : I.IsValid) : Contract where
  pre args mem := args=[I.encode.length] ∧ mem=initMem I.encode ∧ w=wordSize (scratchOuterMultiplier c d) I.encode
  post _ _ ret mem' :=
    let answer := scalingAnswerWords (FlowReduction.arbitraryDemandScalingModel
      ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv I.maxCost I.maxCapacity).value
    ret=answer.length ∧ ListAt mem' 0 answer
  cost _ _ := (scratchArbitraryDemandContract w solver entry T S c d hproc I hv I.maxCost I.maxCapacity).cost [] (fun _ => 0)+
    2000*(I.m+I.n+1)

/-- The entry assembly preserves determinism of the supplied solver. -/
theorem scratchOuterEntryModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body∈scratchOuterEntryModule solver entry b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [outerEntryBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact inputBoundsModule_noRand _ body hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact scratchArbitraryDemandModule_noRand solver entry _ c d hdet body hb
      · have he : body=copyWords := by simpa only [List.mem_singleton] using hb
        subst body
        simp only [copyWords,forRange,forUp,Stmt.NoRand,and_self]

/-- The complete program is deterministic whenever its circulation solver is. -/
theorem scratchOuterScalingProgram_deterministic (solver : Program) (entry c d : ℕ) (hdet : solver.IsDeterministic) :
    (scratchOuterScalingProgram solver entry c d).IsDeterministic := by
  exact scratchOuterEntryModule_noRand solver entry 0 c d hdet

private theorem outer_solve_args {w len heap C U : ℕ} {st : State}
    (h0 : st.regs 0=len) (h1 : st.regs 1=heap)
    (_hlen : len<2^w) (hlen1 : len+1<2^w) (hone : 1<2^w)
    (hC : st.mem len=C) (hU : st.mem (len+1)=U) :
    evalArgs w st [.const 0,.load (.reg 0),.load (.bin .add (.reg 0) (.const 1)),.reg 1]=
      some [0,C,U,heap] := by eval_expr

set_option maxRecDepth 4096 in
/-- Starting from exactly the statement's input, procedure zero returns
the model answer's length and stores that answer at zero, within its
complete solver-plus-linear budget and word multiplier 131072. -/
theorem scratchOuterEntry_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (scratchOuterEntryModule solver entry b c d)) (I : Instance) (hv : I.IsValid) :
    MeetsContract w p b (scratchOuterEntryContract w solver entry T S c d hproc I hv) := by
  let solve := b+1+(inputBoundsModule (b+1)).length
  let copy := solve+(scratchArbitraryDemandModule solver entry solve c d).length
  let region := 2^wordSize (scratchPhaseMultiplier c d) (I.encode++[max I.maxCost 1,(I.m+1)*I.maxCapacity])
  let answer := scalingAnswerWords (FlowReduction.arbitraryDemandScalingModel
    ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv I.maxCost I.maxCapacity).value
  have ht : p.HasAt (b+1) (inputBoundsModule (b+1) ++
      (scratchArbitraryDemandModule solver entry solve c d ++ [copyWords])) := hasAt_tail hp
  have hbounds := hasAt_append_left ht
  have htS : p.HasAt solve (scratchArbitraryDemandModule solver entry solve c d ++ [copyWords]) := hasAt_append_right ht
  have hsolve := hasAt_append_left htS
  have hcopy : p.HasAt copy [copyWords] := hasAt_append_right htS
  have hkB := inputBounds_meetsContract (w := w) hbounds I hv
  have hkS := scratchArbitraryDemand_meetsContract (w := w) hproc hScratch hdet hmono hsolve I hv I.maxCost I.maxCapacity
  have hkC := forwardCopyWords_meetsContract (w := w) hcopy
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl,rfl,hw⟩ := hpre
  change w=wordSize (scratchOuterMultiplier c d) I.encode at hw
  subst w
  have hs := scratch_input_space_wordSize (scratchPhaseMultiplier c d) (scratchPhaseMultiplier_pos c d) I hv
  change I.encode.length+2+10*region<2^wordSize (scratchOuterMultiplier c d) I.encode at hs
  have hg : 16≤region := sixteen_le_source_capacity (scratchPhaseMultiplier c d) _
    (by unfold scratchPhaseMultiplier; have h := scratchWidthFactor_pos c d; omega)
  have hlen := instance_encode_length I hv
  obtain ⟨harg,hpreS⟩ := scratchArbitraryDemand_pre_input_wordSize solver entry T S c d hproc I hv
  obtain ⟨a0,heap0,heq,hat0,hend0,hc,hl,hu,hz0,hspace0⟩ := hpreS
  have ha0 := congrArg (fun xs : List ℕ => xs.getD 0 0) heq
  have hh0 := congrArg (fun xs : List ℕ => xs.getD 3 0) heq
  change 0=a0 at ha0
  change I.encode.length=heap0 at hh0
  subst a0
  subst heap0
  have hC : I.maxCost<2^wordSize (scratchOuterMultiplier c d) I.encode := harg _ (by simp)
  have hU : I.maxCapacity<2^wordSize (scratchOuterMultiplier c d) I.encode := harg _ (by simp)
  have h0 : 0<2^wordSize (scratchOuterMultiplier c d) I.encode := by omega
  have h1 : 1<2^wordSize (scratchOuterMultiplier c d) I.encode := by omega
  have h2 : 2<2^wordSize (scratchOuterMultiplier c d) I.encode := by omega
  have hin : I.encode.length<2^wordSize (scratchOuterMultiplier c d) I.encode := by omega
  have hin1 : I.encode.length+1<2^wordSize (scratchOuterMultiplier c d) I.encode := by omega
  have hin2 : I.encode.length+2<2^wordSize (scratchOuterMultiplier c d) I.encode := by omega
  have hanswerLength : 1≤answer.length ∧ answer.length≤1+2*I.m := by
    dsimp only [answer]
    cases (FlowReduction.arbitraryDemandScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv I.maxCost I.maxCapacity).value with
    | none => exact ⟨by change 1≤1; omega,by change 1≤1+2*I.m; omega⟩
    | some f => rw [scalingAnswerWords_some_length]; omega
  apply runs_start_le
  unfold outerEntryBody
  refine runs_seq_call_le hkB (vs := [0,I.encode.length]) (by eval_expr) (by wram_words)
    ⟨0,I.encode.length,rfl,listAt_initMem _,by omega,by omega,hC,hU,zeroFrom_initMem _,by omega⟩ ?_
  intro heap memB posB hpB
  change (I.encode.length≤heap ∧ heap≤I.encode.length+2 ∧
    (∀ x<I.encode.length,memB x=initMem I.encode x) ∧ ZeroFrom memB heap ∧
    ListAt memB I.encode.length [I.maxCost,I.maxCapacity]) ∧ heap=I.encode.length+2 at hpB
  obtain ⟨⟨_,_,hframeB,hzeroB,hpair⟩,hheap⟩ := hpB
  subst heap
  have hBC : memB I.encode.length=I.maxCost := by simpa using hpair 0 (by change 0<2; omega)
  have hBU : memB (I.encode.length+1)=I.maxCapacity := hpair 1 (by change 1<2; omega)
  have hatB : ListAt memB 0 I.encode :=
    (listAt_initMem _).of_agree_below (by omega : 0+I.encode.length≤I.encode.length) hframeB
  refine runs_seq_call_le hkS (vs := [0,I.maxCost,I.maxCapacity,I.encode.length+2])
    (outer_solve_args rfl rfl hin hin1 h1 hBC hBU) (by wram_words)
    ⟨0,I.encode.length+2,rfl,hatB,by omega,hc,hl,hu,hzeroB,hs⟩ ?_
  intro ret memS posS hpS
  change I.encode.length+2≤ret ∧ ret≤I.encode.length+2+10*region ∧
    ScalingAnswerAt memS (ret-2) ret answer ∧ ZeroFrom memS ret ∧
    (∀ x<I.encode.length+2,memS x=memB x) at hpS
  obtain ⟨hrlo,hrhi,hanswer,_,_⟩ := hpS
  obtain ⟨hheader,ptr,hptr,hptrend,hatAnswer⟩ := hanswer
  have hrw : ret<2^wordSize (scratchOuterMultiplier c d) I.encode := by omega
  have hheadw : ret-2<2^wordSize (scratchOuterMultiplier c d) I.encode := by omega
  have hhead1w : ret-1<2^wordSize (scratchOuterMultiplier c d) I.encode := by omega
  have hptrword : ptr<2^wordSize (scratchOuterMultiplier c d) I.encode := by omega
  have hlengthword : answer.length<2^wordSize (scratchOuterMultiplier c d) I.encode := by omega
  have hreadPtr : memS (ret-2)=ptr := by simpa using hptr 0 (by change 0<2; omega)
  have hreadLength : memS (ret-1)=answer.length := by
    have h := hptr 1 (by change 1<2; omega)
    have he : ret-2+1=ret-1 := by omega
    simpa only [he,List.getElem_cons_succ,List.getElem_cons_zero] using h
  refine runs_seq_assign_le (v := ptr) (by eval_expr) ?_
  refine runs_seq_assign_le (v := answer.length) (by eval_expr) ?_
  refine runs_seq_call_le hkC (vs := [ptr,0,answer.length]) (by eval_expr) (by wram_words)
    ⟨ptr,0,answer.length,rfl,h1,by omega,by omega,Nat.zero_le _⟩ ?_
  intro copied memR posR hpR
  obtain ⟨src,dst,len,heq,_,hcopied,_⟩ := hpR
  have hsrc := congrArg (fun xs : List ℕ => xs.getD 0 0) heq
  have hdst := congrArg (fun xs : List ℕ => xs.getD 1 0) heq
  have hlength := congrArg (fun xs : List ℕ => xs.getD 2 0) heq
  change ptr=src at hsrc
  change 0=dst at hdst
  change answer.length=len at hlength
  subst src
  subst dst
  subst len
  refine runs_ret_le (v := answer.length) (by eval_expr) ?_ ?_
  · exact ⟨rfl,copyWords_listAt hatAnswer rfl hcopied⟩
  · have hcostEq : (scratchArbitraryDemandContract (wordSize (scratchOuterMultiplier c d) I.encode) solver entry T S c d hproc I hv I.maxCost I.maxCapacity).cost
        [0,I.maxCost,I.maxCapacity,I.encode.length+2] memB=
      (scratchArbitraryDemandContract (wordSize (scratchOuterMultiplier c d) I.encode) solver entry T S c d hproc I hv I.maxCost I.maxCapacity).cost [] (fun _ => 0) := rfl
    simp only [scratchOuterEntryContract,inputBoundsContract,forwardCopyWordsContract,copyWordsContract,
      argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
    rw [hcostEq]
    omega

end MinCostFlow.Final
