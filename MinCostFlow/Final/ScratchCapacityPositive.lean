module

public import MinCostFlow.Final.ScratchCapacityScaling
public import MinCostFlow.Scaling.CapacityPositiveContract
import MinCostFlow.Scaling.CapacityScalingProgram
import MinCostFlow.Scaling.CapacityScalingCorrectness
import MinCostFlow.Scaling.CapacityNumericFacts
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.SolverInputLayout
import MinCostFlow.Scaling.CirculationLayout
import WordRAM.Tactic

/-!
# Capacity scaling with inactive edges and polynomial scratch

The wrapper inserts positive-capacity dummy edges, runs the widened
capacity procedure, and erases the dummy entries from the output.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Build the positive instance, solve it, and erase dummy edges. -/
def scratchCapacityPositiveModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  let erase := b+5+(scratchCapacityScalingModule solver entry (b+5) c d).length
  capacityPositiveBody (b+1) (b+5) erase ::
    (positiveInstanceModule (b+1) ++ scratchCapacityScalingModule solver entry (b+5) c d ++ eraseZeroFlowModule erase)

/-- Fresh positive graph, complete capacity reserve, and final erased vector. -/
def scratchCapacityPositiveSpace (c d : ℕ) (J : Circulation) (C U : ℕ) : ℕ :=
  2+5*J.m+scratchCapacityScalingSpace c d J.positiveInstance C U+J.m+2

/-- Exact counted inner-call value as an unsigned array at the final `m`
words. Construction and erasure add explicit linear work to the inner cost. -/
noncomputable def scratchCapacityPositiveContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C U : ℕ) : Contract :=
  let r := J.invokePositive (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U)
  { pre := fun args mem => ∃ a heap,args=[a,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ (∀ x∈J.solverWords,x<2^w) ∧ J.n+1<2^w ∧ 8<2^w ∧
      J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧ 1≤U ∧ ZeroFrom mem heap ∧
      heap+scratchCapacityPositiveSpace c d J C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+scratchCapacityPositiveSpace c d J C U ∧
      ListAt mem' (ret-J.m) (List.ofFn (fun e => (r.value e).toNat)) ∧ ZeroFrom mem' ret ∧
      ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => (scratchCapacityScalingContract w solver entry T S c d hproc J.positiveInstance C U).cost [] (fun _ => 0)+
      400*J.m+900 }

/-- Construction, capacity scaling, and erasure use no random instruction. -/
theorem scratchCapacityPositiveModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchCapacityPositiveModule solver entry b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityPositiveBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | he
    · rcases List.mem_append.mp hb with hp | hs
      · exact positiveInstanceModule_noRand _ body hp
      · exact scratchCapacityScalingModule_noRand solver entry _ c d hdet body hs
    · have heq := List.mem_singleton.mp he
      subst body
      exact eraseZeroFlowBody_noRand _

private theorem positive_count_eval {w a m : ℕ} {st : State}
    (h0 : st.regs 0=a) (ha : a+1<2^w) (hm : st.mem (a+1)=m) :
    Expr.eval w st (.load (.bin .add (.reg 0) (.const 1)))=some m := by eval_expr

private theorem positive_graph_args {w a heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h2 : st.regs 2=heap) :
    evalArgs w st [.reg 0,.reg 2]=some [a,heap] := by eval_expr

private theorem positive_scaling_args {w graph U heap : ℕ} {st : State}
    (h2 : st.regs 2=graph) (h1 : st.regs 1=U) (h4 : st.regs 4=heap) :
    evalArgs w st [.reg 2,.reg 1,.reg 4]=some [graph,U,heap] := by eval_expr

private theorem positive_flow_eval {w heap m : ℕ} {st : State}
    (h5 : st.regs 5=heap) (h3 : st.regs 3=m) (hh : heap<2^w) :
    Expr.eval w st (.bin .sub (.reg 5) (.reg 3))=some (heap-m) := by eval_expr

private theorem positive_erase_args {w a flow m heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h6 : st.regs 6=flow) (h3 : st.regs 3=m) (h5 : st.regs 5=heap)
    (ha : a+2<2^w) (h2 : 2<2^w) :
    evalArgs w st [.bin .add (.reg 0) (.const 2),.reg 6,.reg 3,.reg 5]=some [a+2,flow,m,heap] := by eval_expr

/-- Building the positive instance, invoking the proved full capacity
program, and erasing dummy entries computes the exact counted inner-call
value with explicit linear additional cost. -/
theorem scratchCapacityPositive_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (scratchCapacityPositiveModule solver entry b c d))
    (J : Circulation) (C U : ℕ) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (scratchCapacityPositiveContract w solver entry T S c d hproc J C U) := by
  let solve := (fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)
  let K := J.positiveInstance
  let r := capacityScalingModel solve K U
  have ht := hasAt_tail hp
  have hleft := hasAt_append_left ht
  have hP := hasAt_append_left hleft
  have hS : p.HasAt (b+5) (scratchCapacityScalingModule solver entry (b+5) c d) := by
    have hraw := hasAt_append_right hleft
    have hlen : (positiveInstanceModule (b+1)).length=4 := rfl
    simpa only [hlen,Nat.add_assoc,Nat.reduceAdd] using hraw
  have hE : p.HasAt (b+5+(scratchCapacityScalingModule solver entry (b+5) c d).length)
      (eraseZeroFlowModule (b+5+(scratchCapacityScalingModule solver entry (b+5) c d).length)) := by
    have hraw := hasAt_append_right ht
    have he : b+1+(positiveInstanceModule (b+1) ++ scratchCapacityScalingModule solver entry (b+5) c d).length=
        b+5+(scratchCapacityScalingModule solver entry (b+5) c d).length := by
      rw [List.length_append]
      change b+1+(4+(scratchCapacityScalingModule solver entry (b+5) c d).length)=_
      omega
    rw [he] at hraw
    exact hraw
  have hkP := positiveInstance_meetsContract (w := w) hP J
  have hkS := scratchCapacityScaling_meetsContract (w := w) hproc hScratch hdet hS K C U (J.positiveInstance_costsBounded _ hc)
  have hkE := eraseZeroFlow_meetsContract (w := w) hE J (fun e => (r.value e).toNat) (List.finRange J.m)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hinput,hn1,h8,hC,hu,hU,hz,hspace⟩ := hpre
  have hspaceNum : heap+(2+5*J.m+scratchCapacityScalingSpace c d K C U+J.m+2)<2^w := hspace
  have hcostK := J.positiveInstance_costsBounded C hC
  have huK : ∀ e,K.capacity e≤U := fun e => (J.positiveInstance_capacitiesBounded U hU hu e).2
  have hsolve := fun L (_ : L.CostsBounded (L.m^10))
    (_ : ∀ e,1≤L.capacity e ∧ L.capacity e≤L.m^40) => compressedCanonicalSolverAt_optimal _ solver entry T S (hproc L) L
  have hopt := lemma_C_9 solve hsolve K U (J.positiveInstance_costsBounded _ hc) huK
  have hflowBounds := feasible_unsigned_bounds K r.value U hopt.1 huK
  have hh : heap<2^w := by omega
  have hUword : U<2^w := hwords U (by simp)
  have hmWord : J.m<2^w := by omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have ha2 : a+2<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hM := (solver_header_at J hgraph).2
  have hedge : ListAt mem (a+2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
    simpa only [Nat.add_assoc] using (listAt_cons.mp (listAt_cons.mp hgraph).2).2
  have hcapacities : ∀ e,J.capacity e<2^w := by
    intro e
    exact hinput _ (Circulation.solverEdgeWord_mem J e (by simp [Circulation.solverEdgeWords]))
  apply runs_start_le
  unfold capacityPositiveBody
  refine runs_seq_assign_le (v := J.m) (positive_count_eval (by rfl) ha1 hM) ?_
  refine runs_seq_call_le hkP (vs := [a,heap]) (positive_graph_args (by rfl) (by rfl)) (by wram_words)
    ⟨⟨a,heap,rfl,hgraph,hgraphEnd,hinput,hn1,h8⟩,hz,by change heap+(2+5*J.m)<2^w; omega⟩ ?_
  intro graphHeap memP posP hpostP
  obtain ⟨⟨_,_,hframeP,hzP,hgraphP⟩,hretP⟩ := hpostP
  change graphHeap=heap+2+5*J.m at hretP
  change (∀ x<heap,memP x=mem x) at hframeP
  change ZeroFrom memP graphHeap at hzP
  change ListAt memP heap K.solverWords at hgraphP
  have hgraphWord : graphHeap<2^w := by omega
  have hinnerSpace : graphHeap+scratchCapacityScalingSpace c d K C U<2^w := by omega
  refine runs_seq_call_le hkS (vs := [heap,U,graphHeap])
    (positive_scaling_args (by rfl) (by rfl) (by rfl)) (by wram_words)
    ⟨heap,graphHeap,rfl,hgraphP,by rw [K.solverWords_length]; change heap+(2+5*J.m)≤graphHeap; omega,
      hcostK,huK,hzP,hinnerSpace⟩ ?_
  intro solveHeap memS posS hpostS
  obtain ⟨hloS,hhiS,hflowS,hzS,hframeS⟩ := hpostS
  change graphHeap≤solveHeap at hloS
  change solveHeap≤graphHeap+scratchCapacityScalingSpace c d K C U at hhiS
  change ListAt memS (solveHeap-J.m) (List.ofFn (fun e => (r.value e).toNat)) at hflowS
  change ZeroFrom memS solveHeap at hzS
  change (∀ x<graphHeap,memS x=memP x) at hframeS
  have hsolveWord : solveHeap<2^w := by omega
  have hflowWord : solveHeap-J.m<2^w := by omega
  have hflowEnd : solveHeap-J.m+J.m≤solveHeap := by omega
  have hedgeS : ListAt memS (a+2) ((List.finRange J.m).flatMap J.solverEdgeWords) := by
    apply (hedge.of_agree_below (h₀ := heap) ?_ hframeP).of_agree_below (h₀ := graphHeap) ?_ hframeS
    all_goals rw [Circulation.solverEdgeRecords_length,List.length_finRange]; rw [J.solverWords_length] at hgraphEnd; omega
  have hflowS' : ListAt memS (solveHeap-J.m) ((List.finRange J.m).map (fun e => (r.value e).toNat)) := by
    rwa [←List.ofFn_eq_map]
  refine runs_seq_assign_le (v := solveHeap-J.m) (positive_flow_eval (by rfl) (by rfl) hsolveWord) ?_
  refine runs_seq_call_le hkE (vs := [a+2,solveHeap-J.m,J.m,solveHeap])
    (positive_erase_args (by rfl) (by rfl) (by rfl) (by rfl) ha2 (by omega)) (by wram_words)
    ⟨⟨a+2,solveHeap-J.m,solveHeap,by simp only [List.length_finRange],hedgeS,hflowS',
      by rw [List.length_finRange]; rw [J.solverWords_length] at hgraphEnd; omega,
      by simpa only [List.length_finRange] using hflowEnd,
      (fun e _ => ⟨hcapacities e,(hflowBounds e).2.trans_lt hUword⟩),h8⟩,hzS,
      by change solveHeap+(List.finRange J.m).length<2^w; rw [List.length_finRange]; omega⟩ ?_
  intro ret memE posE hpostE
  obtain ⟨⟨_,_,hframeE,hzE,houtput⟩,hretE⟩ := hpostE
  change ret=solveHeap+(List.finRange J.m).length at hretE
  rw [List.length_finRange] at hretE
  change (∀ x<solveHeap,memE x=memS x) at hframeE
  change ZeroFrom memE ret at hzE
  change ListAt memE solveHeap ((List.finRange J.m).map
    (fun e => if J.capacity e=0 then 0 else (r.value e).toNat)) at houtput
  have hanswer : ListAt memE solveHeap (List.ofFn (fun e =>
      ((J.invokePositive (fun L => capacityScalingModel solve L U)).value e).toNat)) := by
    rw [List.ofFn_eq_map]
    convert houtput using 1
    congr 1
    funext e
    simp only [Circulation.invokePositive,r,K]
    split_ifs <;> rfl
  refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change heap≤ret ∧ ret≤heap+scratchCapacityPositiveSpace c d J C U ∧
      ListAt memE (ret-J.m) (List.ofFn (fun e =>
        ((J.invokePositive (fun L => capacityScalingModel solve L U)).value e).toNat)) ∧
      ZeroFrom memE ret ∧ ∀ x<heap,memE x=mem x
    refine ⟨by omega,by change ret≤heap+(2+5*J.m+scratchCapacityScalingSpace c d K C U+J.m+2); omega,
      ?_,hzE,?_⟩
    · simpa only [hretE,Nat.add_sub_cancel_right] using hanswer
    · intro x hx
      exact (hframeE x (by omega)).trans ((hframeS x (by omega)).trans (hframeP x hx))
  · simp only [scratchCapacityPositiveContract,scratchCapacityScalingContract,positiveInstanceContract,
      eraseZeroFlowContract,heapContract,List.length_finRange,argsSize_cons,argsSize_nil,
      Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,K]
    omega

end MinCostFlow.Final
