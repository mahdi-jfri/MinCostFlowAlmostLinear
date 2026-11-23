module

public import MinCostFlow.Scaling.GeneralScalingContract
import MinCostFlow.Scaling.TwoCallReductionProgram
import MinCostFlow.Scaling.OuterPhaseSpace
import MinCostFlow.Scaling.ScalingSourceWidth
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Executing bounded-demand general-flow scaling

Capacity-order rejection and isolated-demand rejection both return the
failed checked-model answer. On the remaining path, the exact two-call
procedure computes the checked model's result. A preliminary shifted graph
supports the isolated-demand scan and stays in the preserved memory
prefix. All check work and selected solving work are charged explicitly.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

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
theorem generalScaling_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (generalScalingModule solver entry b)) (I : Instance) (hv : I.IsValid) (C U : ℕ) :
    MeetsContract w p b (generalScalingContract w solver entry T hproc I hv C U) := by
  let graphBase := b+3
  let isolated := graphBase+(shiftedGraphModule graphBase).length
  let solve := isolated+(isolatedCheckModule isolated).length
  let failure := solve+(twoCallReductionModule solver entry solve).length
  let K := max C 1
  let region := 2^wordSize 16384 (I.encode++[K,U])
  let J := FlowReduction.shiftedGraph I hv
  let r := FlowReduction.generalScalingModel (canonicalSolver solver entry T hproc) I hv C U
  let flag := if FlowReduction.isolatedCheck I hv then 1 else 0
  let S := (twoCallReductionContract w solver entry T hproc I hv K U).cost [] (fun _ => 0)
  have ht : p.HasAt (b+1) (capacityCheckModule (b+1) ++ (shiftedGraphModule graphBase ++
      (isolatedCheckModule isolated ++ (twoCallReductionModule solver entry solve ++ infeasibleResultModule failure)))) := hasAt_tail hp
  have hcheck := hasAt_append_left ht
  have htG : p.HasAt graphBase (shiftedGraphModule graphBase ++
      (isolatedCheckModule isolated ++ (twoCallReductionModule solver entry solve ++ infeasibleResultModule failure))) := hasAt_append_right ht
  have hgraph := hasAt_append_left htG
  have htI : p.HasAt isolated (isolatedCheckModule isolated ++
      (twoCallReductionModule solver entry solve ++ infeasibleResultModule failure)) := hasAt_append_right htG
  have hisolated := hasAt_append_left htI
  have htS : p.HasAt solve (twoCallReductionModule solver entry solve ++ infeasibleResultModule failure) := hasAt_append_right htI
  have hsolve := hasAt_append_left htS
  have hfailure : p.HasAt failure (infeasibleResultModule failure) := hasAt_append_right htS
  have hkC := capacityCheck_meetsContract (w := w) hcheck I.edges
  have hkG := shiftedGraph_meetsContract (w := w) hgraph I hv
  have hkI := isolatedCheck_meetsContract (w := w) hisolated I hv
  have hkS := twoCallReduction_meetsContract (w := w) hproc hdet hmono hsolve I hv K U
  have hkN := infeasibleResult_meetsContract (w := w) hfailure
  have hG : 16≤region := sixteen_le_source_capacity 16384 _ (by decide)
  have hencode := instance_encode_length I hv
  have hsourceLen := length_lt_two_pow_wordSize (by decide : 1≤16384) (I.encode++[K,U])
  change (I.encode++[K,U]).length<region at hsourceLen
  have hcheckSpace : 4+5*I.m+I.n≤region := by
    simp only [List.length_append,List.length_cons,List.length_nil,hencode] at hsourceLen
    omega
  have hsourceWords : ∀ x∈I.encode,x<region := fun x hx =>
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_left _ hx)
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
  have hSCost : ∀ args mem,(twoCallReductionContract w solver entry T hproc I hv K U).cost args mem=S := fun _ _ => rfl
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
      obtain ⟨_,hpreF⟩ := feasibilityPhase_pre_of_source_space solver entry T hproc I hv K U a heap mem
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
              (if FlowReduction.isolatedCheck I hv then S else 50) else 50)
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
              (fun Q => costCapacityModel (canonicalSolver solver entry T hproc) Q K
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
                (if FlowReduction.isolatedCheck I hv then S else 50) else 50)
              rw [ite_eq_left hcap]
              simp only [hiso,↓reduceIte]
              rw [hSCost]
              have hlen : I.edges.length=I.m := rfl
              rw [hlen]
              omega

end MinCostFlow.Scaling.Machine
