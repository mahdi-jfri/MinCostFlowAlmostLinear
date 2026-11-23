module

public import MinCostFlow.Scaling.OuterEntryContract
import MinCostFlow.Scaling.ArbitraryDemandProgram
import MinCostFlow.Scaling.ArbitraryDemandInputWordSize
import MinCostFlow.Scaling.ScalingSourceWidth
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Executing scaling from the required input

The entry computes the exact bounds in two fresh cells, then runs the
proved arbitrary-demand procedure at the same fixed word width. Its
internal answer header supplies the copy length and source. Forward
copying puts the exact model answer at address zero, as required by the
whole-program machine interface.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

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
theorem outerEntry_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (outerEntryModule solver entry b)) (I : Instance) (hv : I.IsValid) :
    MeetsContract w p b (outerEntryContract w solver entry T hproc I hv) := by
  let solve := b+1+(inputBoundsModule (b+1)).length
  let copy := solve+(arbitraryDemandModule solver entry solve).length
  let region := 2^wordSize 16384 (I.encode++[max I.maxCost 1,(I.m+1)*I.maxCapacity])
  let answer := scalingAnswerWords (FlowReduction.arbitraryDemandScalingModel
    (canonicalSolver solver entry T hproc) I hv I.maxCost I.maxCapacity).value
  have ht : p.HasAt (b+1) (inputBoundsModule (b+1) ++
      (arbitraryDemandModule solver entry solve ++ [copyWords])) := hasAt_tail hp
  have hbounds := hasAt_append_left ht
  have htS : p.HasAt solve (arbitraryDemandModule solver entry solve ++ [copyWords]) := hasAt_append_right ht
  have hsolve := hasAt_append_left htS
  have hcopy : p.HasAt copy [copyWords] := hasAt_append_right htS
  have hkB := inputBounds_meetsContract (w := w) hbounds I hv
  have hkS := arbitraryDemand_meetsContract (w := w) hproc hdet hmono hsolve I hv I.maxCost I.maxCapacity
  have hkC := forwardCopyWords_meetsContract (w := w) hcopy
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl,rfl,hw⟩ := hpre
  change w=wordSize 131072 I.encode at hw
  subst w
  have hs := arbitraryDemand_input_space_wordSize I hv
  change I.encode.length+2+10*region<2^wordSize 131072 I.encode at hs
  have hg : 16≤region := sixteen_le_source_capacity 16384 _ (by decide)
  have hlen := instance_encode_length I hv
  obtain ⟨harg,hpreS⟩ := arbitraryDemand_pre_input_wordSize solver entry T hproc I hv
  obtain ⟨a0,heap0,heq,hat0,hend0,hc,hl,hu,hz0,hspace0⟩ := hpreS
  have ha0 := congrArg (fun xs : List ℕ => xs.getD 0 0) heq
  have hh0 := congrArg (fun xs : List ℕ => xs.getD 3 0) heq
  change 0=a0 at ha0
  change I.encode.length=heap0 at hh0
  subst a0
  subst heap0
  have hC : I.maxCost<2^wordSize 131072 I.encode := harg _ (by simp)
  have hU : I.maxCapacity<2^wordSize 131072 I.encode := harg _ (by simp)
  have h0 : 0<2^wordSize 131072 I.encode := by omega
  have h1 : 1<2^wordSize 131072 I.encode := by omega
  have h2 : 2<2^wordSize 131072 I.encode := by omega
  have hin : I.encode.length<2^wordSize 131072 I.encode := by omega
  have hin1 : I.encode.length+1<2^wordSize 131072 I.encode := by omega
  have hin2 : I.encode.length+2<2^wordSize 131072 I.encode := by omega
  have hanswerLength : 1≤answer.length ∧ answer.length≤1+2*I.m := by
    dsimp only [answer]
    cases (FlowReduction.arbitraryDemandScalingModel (canonicalSolver solver entry T hproc) I hv I.maxCost I.maxCapacity).value with
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
  have hrw : ret<2^wordSize 131072 I.encode := by omega
  have hheadw : ret-2<2^wordSize 131072 I.encode := by omega
  have hhead1w : ret-1<2^wordSize 131072 I.encode := by omega
  have hptrword : ptr<2^wordSize 131072 I.encode := by omega
  have hlengthword : answer.length<2^wordSize 131072 I.encode := by omega
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
  · have hcostEq : (arbitraryDemandContract (wordSize 131072 I.encode) solver entry T hproc I hv I.maxCost I.maxCapacity).cost
        [0,I.maxCost,I.maxCapacity,I.encode.length+2] memB=
      (arbitraryDemandContract (wordSize 131072 I.encode) solver entry T hproc I hv I.maxCost I.maxCapacity).cost [] (fun _ => 0) := rfl
    simp only [outerEntryContract,inputBoundsContract,forwardCopyWordsContract,copyWordsContract,
      argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
    rw [hcostEq]
    omega

end MinCostFlow.Scaling.Machine
