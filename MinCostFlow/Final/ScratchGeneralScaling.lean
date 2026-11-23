module

public import MinCostFlow.Final.ScratchTwoCallReduction
public import MinCostFlow.Scaling.GeneralScalingContract
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.OuterPhaseSpace
import MinCostFlow.Scaling.ScalingSourceWidth
import MinCostFlow.Scaling.TwoCallReductionProgram
import WordRAM.Entry
import WordRAM.Tactic

/-!
# Bounded-demand scaling with polynomial scratch

The entry checks capacity order and isolated demands before calling
the two-phase reduction.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Capacity order, shifted graph, isolated demands, complete two-call
scaling, and failed-answer serialization. -/
def scratchGeneralScalingModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  let graph := b+3
  let isolated := graph+(shiftedGraphModule graph).length
  let solve := isolated+(isolatedCheckModule isolated).length
  let failure := solve+(scratchTwoCallReductionModule solver entry solve c d).length
  generalScalingBody (b+1) graph isolated solve failure ::
    (capacityCheckModule (b+1) ++ (shiftedGraphModule graph ++
      (isolatedCheckModule isolated ++ (scratchTwoCallReductionModule solver entry solve c d ++ infeasibleResultModule failure))))

/-- The exact bounded-demand general model, including isolated demands
and inconsistent capacities, with only the selected inner cost charged. -/
noncomputable def scratchGeneralScalingContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (I : Instance) (hv : I.IsValid) (C U : ℕ) : Contract :=
  let region := 2^wordSize (scratchPhaseMultiplier c d) (I.encode++[max C 1,U])
  { pre := fun args mem => ∃ a heap,args=[a,C,U,heap] ∧ ListAt mem a I.encode ∧ a+I.encode.length≤heap ∧
      (∀ e,(I.edge e).cost.natAbs≤C) ∧ (∀ v : Fin I.n,(I.d v).natAbs≤U) ∧
      (∀ e,(I.edge e).lower.natAbs≤U) ∧ (∀ e,(I.edge e).upper.natAbs≤U) ∧
      ZeroFrom mem heap ∧ heap+8*region<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+8*region ∧
      ScalingAnswerAt mem' (ret-2) ret
        (scalingAnswerWords (FlowReduction.generalScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv C U).value) ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => 2000*(I.m+I.n+1)+
      if ∀ e,(I.edge e).lower≤(I.edge e).upper then
        (if FlowReduction.isolatedCheck I hv then
          (scratchTwoCallReductionContract w solver entry T S c d hproc I hv (max C 1) U).cost [] (fun _ => 0)
        else 50)
      else 50 }

/-- The bounded-demand general scaling module uses no random instruction
whenever its supplied bounded circulation solver does not. -/
theorem scratchGeneralScalingModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body∈scratchGeneralScalingModule solver entry b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [generalScalingBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact capacityCheckModule_noRand _ body hb
    · rcases List.mem_append.mp hb with hb | hb
      · exact shiftedGraphModule_noRand _ body hb
      · rcases List.mem_append.mp hb with hb | hb
        · exact isolatedCheckModule_noRand _ body hb
        · rcases List.mem_append.mp hb with hb | hb
          · exact scratchTwoCallReductionModule_noRand solver entry _ c d hdet body hb
          · exact infeasibleResultModule_noRand _ body hb

private theorem general_count_eval {w a m : ℕ} {st : State}
    (h0 : st.regs 0=a) (ha : a+1<2^w) (hm : st.mem (a+1)=m) :
    Expr.eval w st (.load (.bin .add (.reg 0) (.const 1)))=some m := by eval_expr

private theorem general_cost_eval {w C : ℕ} {st : State}
    (h1 : st.regs 1=C) (hone : 1<2^w) (hc : max C 1<2^w) :
    Expr.eval w st (.bin .add (.reg 1) (.bin .eq (.reg 1) (.const 0)))=some (max C 1) := by
  have heq : C+(if C=0 then 1 else 0)=max C 1 := by
    by_cases hz : C=0
    · simp only [hz,↓reduceIte,Nat.zero_add,Nat.zero_max]
    · rw [ite_eq_right hz,max_eq_left (by omega),Nat.add_zero]
  apply Expr.eval_eq_of_eq (v₁ := C+(if C=0 then 1 else 0)) ?_ heq
  exact Expr.eval_add (Expr.eval_reg_of_eq h1)
    (Expr.eval_eq_op (Expr.eval_reg_of_eq h1) (Expr.eval_const (by omega)) hone)
    (by rw [heq]; exact hc)

private theorem general_check_args {w a m : ℕ} {st : State}
    (h0 : st.regs 0=a) (h4 : st.regs 4=m) (ha : a+2<2^w) (h2 : 2<2^w) :
    evalArgs w st [.bin .add (.reg 0) (.const 2),.reg 4]=some [a+2,m] := by eval_expr

private theorem general_isolated_eval {w ptr flag : ℕ} {st : State}
    (h7 : st.regs 7=ptr) (hp : ptr+1<2^w) (h1 : 1<2^w) (hc : st.mem (ptr+1)=flag) :
    Expr.eval w st (.load (.bin .add (.reg 7) (.const 1)))=some flag := by eval_expr

set_option maxRecDepth 4096 in
/-- The complete bounded-demand procedure computes exactly
`generalScalingModel`, with both checked rejection paths, a shared answer
header, full memory frames, and the selected branch's counted cost. -/
theorem scratchGeneralScaling_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (scratchGeneralScalingModule solver entry b c d)) (I : Instance) (hv : I.IsValid) (C U : ℕ) :
    MeetsContract w p b (scratchGeneralScalingContract w solver entry T S c d hproc I hv C U) := by
  let graphBase := b+3
  let isolated := graphBase+(shiftedGraphModule graphBase).length
  let solve := isolated+(isolatedCheckModule isolated).length
  let failure := solve+(scratchTwoCallReductionModule solver entry solve c d).length
  let K := max C 1
  let region := 2^wordSize (scratchPhaseMultiplier c d) (I.encode++[K,U])
  let J := FlowReduction.shiftedGraph I hv
  let r := FlowReduction.generalScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) I hv C U
  let flag := if FlowReduction.isolatedCheck I hv then 1 else 0
  let charge := (scratchTwoCallReductionContract w solver entry T S c d hproc I hv K U).cost [] (fun _ => 0)
  have ht : p.HasAt (b+1) (capacityCheckModule (b+1) ++ (shiftedGraphModule graphBase ++
      (isolatedCheckModule isolated ++ (scratchTwoCallReductionModule solver entry solve c d ++ infeasibleResultModule failure)))) := hasAt_tail hp
  have hcheck := hasAt_append_left ht
  have htG : p.HasAt graphBase (shiftedGraphModule graphBase ++
      (isolatedCheckModule isolated ++ (scratchTwoCallReductionModule solver entry solve c d ++ infeasibleResultModule failure))) := hasAt_append_right ht
  have hgraph := hasAt_append_left htG
  have htI : p.HasAt isolated (isolatedCheckModule isolated ++
      (scratchTwoCallReductionModule solver entry solve c d ++ infeasibleResultModule failure)) := hasAt_append_right htG
  have hisolated := hasAt_append_left htI
  have htS : p.HasAt solve (scratchTwoCallReductionModule solver entry solve c d ++ infeasibleResultModule failure) := hasAt_append_right htI
  have hsolve := hasAt_append_left htS
  have hfailure : p.HasAt failure (infeasibleResultModule failure) := hasAt_append_right htS
  have hkC := capacityCheck_meetsContract (w := w) hcheck I.edges
  have hkG := shiftedGraph_meetsContract (w := w) hgraph I hv
  have hkI := isolatedCheck_meetsContract (w := w) hisolated I hv
  have hkS := scratchTwoCallReduction_meetsContract (w := w) hproc hScratch hdet hmono hsolve I hv K U
  have hkN := infeasibleResult_meetsContract (w := w) hfailure
  have hG : 16≤region := sixteen_le_source_capacity (scratchPhaseMultiplier c d) _
    (by unfold scratchPhaseMultiplier; have h := scratchWidthFactor_pos c d; omega)
  have hencode := instance_encode_length I hv
  have hsourceLen := length_lt_two_pow_wordSize (scratchPhaseMultiplier_pos c d) (I.encode++[K,U])
  change (I.encode++[K,U]).length<region at hsourceLen
  have hcheckSpace : 4+5*I.m+I.n≤region := by
    simp only [List.length_append,List.length_cons,List.length_nil,hencode] at hsourceLen
    omega
  have hsourceWords : ∀ x∈I.encode,x<region := fun x hx =>
    lt_two_pow_wordSize_of_mem (scratchPhaseMultiplier_pos c d) (List.mem_append_left _ hx)
  have hK : 1≤K := le_max_right _ _
  have hSK : max K 1=K := max_eq_left hK
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hat,hend,hcost,hd,hl,hu,hz,hs⟩ := hpre
  change heap+8*region<2^w at hs
  have hGH : region<2^w := by omega
  have h8 : 8<2^w := by omega
  have hh : heap<2^w := by omega
  have ha : a<2^w := by omega
  have ha1 : a+1<2^w := by rw [hencode] at hend; omega
  have ha2 : a+2<2^w := by rw [hencode] at hend; omega
  have hm : I.m<2^w := by rw [hencode] at hend; omega
  have hCword := hwords C (by simp)
  have hKword : K<2^w := max_lt hCword (by omega)
  have hUword := hwords U (by simp)
  have hM := (instance_header_at I mem a hat).2
  have hedge := instance_edges_at I mem a hat
  have hIwords : ∀ x∈I.encode,x<2^w := fun x hx => (hsourceWords x hx).trans hGH
  have hCost : ∀ e,(I.edge e).cost.natAbs≤K := fun e => (hcost e).trans (le_max_left _ _)
  have hSCost : ∀ args mem,(scratchTwoCallReductionContract w solver entry T S c d hproc I hv K U).cost args mem=charge := fun _ _ => rfl
  apply runs_start_le
  unfold generalScalingBody
  refine runs_seq_assign_le (v := I.m) (general_count_eval (by rfl) ha1 hM) ?_
  refine runs_seq_assign_le (v := K) (general_cost_eval (by rfl) (by omega) hKword) ?_
  refine runs_seq_call_le hkC (vs := [a+2,I.m]) (general_check_args (by rfl) (by rfl) ha2 (by omega))
    (by wram_words) ?_ ?_
  · refine ⟨a+2,rfl,hedge,?_,h8,?_⟩
    · change a+2+8*I.m<2^w
      rw [hencode] at hend; omega
    · intro x hx
      exact hIwords x (instance_edges_word_mem I hx)
  · intro capFlag memC posC hpostC
    obtain ⟨hmemC,hcapFlag⟩ := hpostC
    change memC=mem at hmemC
    subst memC
    change capFlag=(if ∀ e∈I.edges,e.lower≤e.upper then 1 else 0) at hcapFlag
    wram_step
    · have hcap : ¬∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper := by
        intro hc
        rw [ite_eq_left ((instance_capacity_order_iff I).mp hc)] at hcapFlag
        omega
      have hmodel : r.value=none := by
        unfold r FlowReduction.generalScalingModel FlowReduction.checkedMeasured
        split
        · dsimp only
          unfold FlowReduction.reduceMeasured
          rw [ite_eq_right hcap]
        · rfl
      refine runs_seq_call_le hkN (vs := [heap]) (by eval_expr) (by wram_words)
        ⟨⟨heap,rfl⟩,hz,by change heap+3<2^w; omega⟩ ?_
      intro out memN posN hpostN
      obtain ⟨⟨_,_,hframeN,hzN,_⟩,hout,hanswer⟩ := hpostN
      change out=heap+3 at hout
      change (∀ x<heap,memN x=mem x) at hframeN
      change ZeroFrom memN out at hzN
      have how : out<2^w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change heap≤out ∧ out≤heap+8*region ∧ ScalingAnswerAt memN (out-2) out (scalingAnswerWords r.value) ∧
          ZeroFrom memN out ∧ ∀ x<heap,memN x=mem x
        rw [hmodel]
        exact ⟨by omega,by omega,hanswer,hzN,hframeN⟩
      · simp only [capacityCheckContract,infeasibleResultContract,heapContract,argsSize_cons,argsSize_nil,
          Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        change _≤2000*(I.m+I.n+1)+(if ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper then _ else 50)
        rw [ite_eq_right hcap]
        have hlen : I.edges.length=I.m := rfl
        rw [hlen]
        omega
    · have hcapList : ∀ e∈I.edges,e.lower≤e.upper := by
        by_contra hn
        rw [ite_eq_right hn] at hcapFlag
        exact hcond hcapFlag
      have hcap := (instance_capacity_order_iff I).mpr hcapList
      have hlList : ∀ e∈I.edges,e.lower.natAbs≤U := by
        intro e he
        obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp he
        exact hl ⟨i,hi⟩
      have huList : ∀ e∈I.edges,e.upper.natAbs≤U := by
        intro e he
        obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp he
        exact hu ⟨i,hi⟩
      obtain ⟨_,hpreF⟩ := scratchFeasibilityPhase_pre_of_source_space solver entry T S c d hproc I hv K U a heap mem
        hK hcapList hd hlList huList hat hend hz (by change heap+region<2^w; omega)
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hbudget,_,_,_,_,_⟩ := hpreF
      have hsum := capacity_sum_words I hlList huList hbudget
      have hJwords := shiftedGraph_words I hv hIwords hlList huList hbudget
      refine runs_seq_call_le hkG (vs := [a,heap]) (by eval_expr) (by wram_words)
        ⟨⟨a,heap,rfl,hat,hend,hcapList,hsum,hIwords,h8⟩,hz,
          by change heap+(2+5*I.m)<2^w; omega⟩ ?_
      intro graphEnd memG posG hpostG
      obtain ⟨⟨_,_,hframeG,hzG,hgraphG⟩,hgraphEnd⟩ := hpostG
      change graphEnd=heap+2+5*I.m at hgraphEnd
      change ListAt memG heap J.solverWords at hgraphG
      change (∀ x<heap,memG x=mem x) at hframeG
      change ZeroFrom memG graphEnd at hzG
      have hgWord : graphEnd<2^w := by omega
      have hinputG := hat.of_agree_below hend hframeG
      refine runs_seq_call_le hkI (vs := [a,heap,graphEnd]) (by eval_expr) (by wram_words) ?_ ?_
      · refine ⟨⟨a,heap,graphEnd,rfl,hinputG,hgraphG,by omega,?_,hIwords,hJwords,h8⟩,hzG,?_⟩
        · rw [J.solverWords_length]
          change heap+(2+5*I.m)≤graphEnd
          omega
        · change graphEnd+(I.n+2)<2^w; omega
      · intro labelsEnd memI posI hpostI
        obtain ⟨⟨_,_,hframeI,hzI,hflagI,_,_⟩,hlabelsEnd⟩ := hpostI
        change labelsEnd=graphEnd+2+I.n at hlabelsEnd
        change memI (graphEnd+1)=flag at hflagI
        change (∀ x<graphEnd,memI x=memG x) at hframeI
        change ZeroFrom memI labelsEnd at hzI
        have hlWord : labelsEnd<2^w := by omega
        have hflagPtr : graphEnd+1<2^w := by omega
        refine runs_seq_assign_le (v := flag) (general_isolated_eval (by rfl) hflagPtr (by omega) hflagI) ?_
        wram_step
        · have hiso : FlowReduction.isolatedCheck I hv=false := by
            by_contra hn
            have ht := Bool.eq_true_of_not_eq_false hn
            have hf : flag=1 := by simp only [flag,ht,↓reduceIte]
            omega
          have hmodel : r.value=none := by
            unfold r FlowReduction.generalScalingModel FlowReduction.checkedMeasured
            simp only [hiso,Bool.false_eq_true,↓reduceIte]
          refine runs_seq_call_le hkN (vs := [labelsEnd]) (by eval_expr) (by wram_words)
            ⟨⟨labelsEnd,rfl⟩,hzI,by change labelsEnd+3<2^w; omega⟩ ?_
          intro out memN posN hpostN
          obtain ⟨⟨_,_,hframeN,hzN,_⟩,hout,hanswer⟩ := hpostN
          change out=labelsEnd+3 at hout
          change (∀ x<labelsEnd,memN x=memI x) at hframeN
          change ZeroFrom memN out at hzN
          have how : out<2^w := by omega
          refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
          · change heap≤out ∧ out≤heap+8*region ∧ ScalingAnswerAt memN (out-2) out (scalingAnswerWords r.value) ∧
              ZeroFrom memN out ∧ ∀ x<heap,memN x=mem x
            rw [hmodel]
            refine ⟨by omega,by omega,hanswer,hzN,?_⟩
            intro x hx
            exact (hframeN x (by omega)).trans ((hframeI x (by omega)).trans (hframeG x hx))
          · simp only [capacityCheckContract,shiftedGraphContract,isolatedCheckContract,infeasibleResultContract,
              heapContract,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
            change _≤2000*(I.m+I.n+1)+(if ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper then
              (if FlowReduction.isolatedCheck I hv then charge else 50) else 50)
            rw [ite_eq_left hcap]
            simp only [hiso,Bool.false_eq_true,↓reduceIte]
            have hlen : I.edges.length=I.m := rfl
            rw [hlen]
            omega
        · have hiso : FlowReduction.isolatedCheck I hv=true := by
            by_contra hn
            have hf : flag=0 := by simp only [flag,Bool.eq_false_iff.mpr hn,Bool.false_eq_true,↓reduceIte]
            exact hcond hf
          have hmodel : r.value=(FlowReduction.reduceMeasured (Circulation.invokePruned
              (fun Q => costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) Q K
                (FlowReduction.scalingCapacityBudget I U))) I hv).value := by
            unfold r FlowReduction.generalScalingModel FlowReduction.checkedMeasured
            simp only [hiso,↓reduceIte]
            rfl
          have hinputI := hinputG.of_agree_below (h₀ := graphEnd) (by omega) hframeI
          refine runs_seq_call_le hkS (vs := [a,K,U,labelsEnd]) (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨a,labelsEnd,rfl,hinputI,by omega,hK,hCost,hd,hl,hu,hzI,
              by change labelsEnd+4*region<2^w; omega⟩
          · intro out memS posS hpostS
            obtain ⟨hlo,hhi,hanswer,hzS,hframeS⟩ := hpostS
            change labelsEnd≤out at hlo
            change out≤labelsEnd+4*region at hhi
            change (∀ x<labelsEnd,memS x=memI x) at hframeS
            change ZeroFrom memS out at hzS
            have how : out<2^w := by omega
            refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
            · change heap≤out ∧ out≤heap+8*region ∧ ScalingAnswerAt memS (out-2) out (scalingAnswerWords r.value) ∧
                ZeroFrom memS out ∧ ∀ x<heap,memS x=mem x
              rw [hmodel]
              refine ⟨by omega,by omega,hanswer,hzS,?_⟩
              intro x hx
              exact (hframeS x (by omega)).trans ((hframeI x (by omega)).trans (hframeG x hx))
            · simp only [capacityCheckContract,shiftedGraphContract,isolatedCheckContract,
                heapContract,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
              change _≤2000*(I.m+I.n+1)+(if ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper then
                (if FlowReduction.isolatedCheck I hv then charge else 50) else 50)
              rw [ite_eq_left hcap]
              simp only [hiso,↓reduceIte]
              rw [hSCost]
              have hlen : I.edges.length=I.m := rfl
              rw [hlen]
              omega

end MinCostFlow.Final
