module

public import MinCostFlow.Scaling.TwoCallReductionContract
import MinCostFlow.Scaling.TwoCallReductionFacts
import MinCostFlow.Scaling.FeasibilityPhaseProgram
import MinCostFlow.Scaling.ResidualOptimizationProgram
import MinCostFlow.Scaling.OuterPhaseSpace
import MinCostFlow.Scaling.ScalingSourceWidth
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Executing the exact two-call general-flow reduction

Capacity-order failure returns the infeasible answer immediately. Otherwise
execute the complete feasibility phase, use its exact stored branch flag,
and either report failure or pass its unsigned original-edge prefix to
residual optimization. The successful signed flow is serialized in the
statement's answer format. Each path is charged only for calls it executes.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem two_call_m_eval {w a m : ℕ} {st : State}
    (h0 : st.regs 0=a) (ha : a+1<2^w) (hm : st.mem (a+1)=m) :
    Expr.eval w st (.load (.bin .add (.reg 0) (.const 1)))=some m := by eval_expr

private theorem two_call_check_args {w a m : ℕ} {st : State}
    (h0 : st.regs 0=a) (h4 : st.regs 4=m) (ha : a+2<2^w) (h2 : 2<2^w) :
    evalArgs w st [.bin .add (.reg 0) (.const 2),.reg 4]=some [a+2,m] := by eval_expr

private theorem two_call_header_eval {w ret : ℕ} {st : State}
    (h6 : st.regs 6=ret) (hr : ret<2^w) (h3 : 3<2^w) :
    Expr.eval w st (.bin .sub (.reg 6) (.const 3))=some (ret-3) := by eval_expr

private theorem two_call_flag_eval {w ptr flag : ℕ} {st : State}
    (h7 : st.regs 7=ptr) (_hp : ptr<2^w) (hc : st.mem ptr=flag) :
    Expr.eval w st (.load (.reg 7))=some flag := by eval_expr

private theorem two_call_flow_eval {w ptr flow : ℕ} {st : State}
    (h7 : st.regs 7=ptr) (hp : ptr+1<2^w) (h1 : 1<2^w) (hc : st.mem (ptr+1)=flow) :
    Expr.eval w st (.load (.bin .add (.reg 7) (.const 1)))=some flow := by eval_expr

private theorem two_call_graph_eval {w ptr graph : ℕ} {st : State}
    (h7 : st.regs 7=ptr) (hp : ptr+2<2^w) (h2 : 2<2^w) (hc : st.mem (ptr+2)=graph) :
    Expr.eval w st (.load (.bin .add (.reg 7) (.const 2)))=some graph := by eval_expr

private theorem two_call_success_args {w ret m : ℕ} {st : State}
    (h11 : st.regs 11=ret) (h4 : st.regs 4=m) (hr : ret<2^w) (h2 : 2<2^w) (hm : 2*m<2^w) :
    evalArgs w st [.bin .sub (.reg 11) (.bin .mul (.const 2) (.reg 4)),.reg 4,.reg 11]=
      some [ret-2*m,m,ret] := by eval_expr

set_option maxRecDepth 4096 in
/-- The complete two-call procedure writes exactly the counted reduction's
answer, with four shared phase regions, full memory frames, and the
branch-sensitive contract cost. -/
theorem twoCallReduction_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (twoCallReductionModule solver entry b)) (I : Instance) (hv : I.IsValid) (C U : ℕ) :
    MeetsContract w p b (twoCallReductionContract w solver entry T hproc I hv C U) := by
  let first := b+3
  let second := first+(feasibilityPhaseModule solver entry first).length
  let success := second+(residualOptimizationModule solver entry second).length
  let failure := success+(flowResultModule success).length
  let region := 2^wordSize 16384 (I.encode++[C,U])
  let B := FlowReduction.scalingCapacityBudget I U
  let inner := fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C B
  let P := FlowReduction.buildFeasibilityInstance I hv
  let g := (Circulation.invokePruned inner P).value
  let f := fun e => g (Fin.castAdd (I.n+I.n) e)
  let delta := (Circulation.invokePruned inner ((FlowReduction.shiftedGraph I hv).residual f)).value
  let result := fun e => (I.edge e).lower+f e+delta (Fin.castAdd I.m e)-delta (Fin.natAdd I.m e)
  let good := P.integerObjective g = -((FlowReduction.shiftedGraph I hv).demandMass (FlowReduction.shiftedDemand I) : ℤ)
  let flag := if good then 1 else 0
  let r := FlowReduction.reduceMeasured (Circulation.invokePruned inner) I hv
  let F := (feasibilityPhaseContract w solver entry T hproc I hv C U).cost [] (fun _ => 0)
  let O := (residualOptimizationContract w solver entry T hproc I hv f C U).cost [] (fun _ => 0)
  have ht : p.HasAt (b+1) (capacityCheckModule (b+1) ++ (feasibilityPhaseModule solver entry first ++
      (residualOptimizationModule solver entry second ++
        (flowResultModule success ++ infeasibleResultModule failure)))) := hasAt_tail hp
  have hcheck := hasAt_append_left ht
  have htF : p.HasAt first (feasibilityPhaseModule solver entry first ++
      (residualOptimizationModule solver entry second ++
        (flowResultModule success ++ infeasibleResultModule failure))) := hasAt_append_right ht
  have hfirst := hasAt_append_left htF
  have htO : p.HasAt second (residualOptimizationModule solver entry second ++
      (flowResultModule success ++ infeasibleResultModule failure)) := hasAt_append_right htF
  have hsecond := hasAt_append_left htO
  have htS : p.HasAt success (flowResultModule success ++ infeasibleResultModule failure) := hasAt_append_right htO
  have hsuccess := hasAt_append_left htS
  have hfailure : p.HasAt failure (infeasibleResultModule failure) := hasAt_append_right htS
  have hkC := capacityCheck_meetsContract (w := w) hcheck I.edges
  have hkF := feasibilityPhase_meetsContract (w := w) hproc hdet hmono hfirst I hv C U
  have hkO := residualOptimization_meetsContract (w := w) hproc hdet hmono hsecond I hv f C U
  have hkS := flowResult_meetsContract (w := w) hsuccess result
  have hkN := infeasibleResult_meetsContract (w := w) hfailure
  have hG : 16≤region := sixteen_le_source_capacity 16384 _ (by decide)
  have hencode := instance_encode_length I hv
  have hsourceLen := length_lt_two_pow_wordSize (by decide : 1≤16384) (I.encode++[C,U])
  have hanswerSize : 3+2*I.m≤region := by
    simp only [List.length_append,List.length_cons,List.length_nil,hencode] at hsourceLen
    omega
  have hsourceWords : ∀ x∈I.encode,x<region := fun x hx =>
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_left _ hx)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hat,hend,hC,hcost,hd,hl,hu,hz,hs⟩ := hpre
  change heap+4*region<2^w at hs
  have hGH : region<2^w := by omega
  have h8 : 8<2^w := by omega
  have hh : heap<2^w := by omega
  have ha : a<2^w := by omega
  have ha1 : a+1<2^w := by rw [hencode] at hend; omega
  have ha2 : a+2<2^w := by rw [hencode] at hend; omega
  have hm : I.m<2^w := by rw [hencode] at hend; omega
  have h2m : 2*I.m<2^w := by omega
  have hM := (instance_header_at I mem a hat).2
  have hedge := instance_edges_at I mem a hat
  have hfBounds := feasibilityPhase_restrict_bounds solver entry T hproc I hv C U hC hd hl hu
  change (∀ e,0≤f e ∧ f e≤((FlowReduction.shiftedGraph I hv).capacity e : ℤ)) at hfBounds
  have hOspace : residualOptimizationSpace I hv f C U≤region :=
    residualOptimizationSpace_le_source_capacity solver entry T hproc I hv f C U hfBounds hcost hl hu
  have hFCost : ∀ args mem,(feasibilityPhaseContract w solver entry T hproc I hv C U).cost args mem=F := fun _ _ => rfl
  have hOCost : ∀ args mem,(residualOptimizationContract w solver entry T hproc I hv f C U).cost args mem=O := fun _ _ => rfl
  apply runs_start_le
  unfold twoCallReductionBody
  refine runs_seq_assign_le (v := I.m) (two_call_m_eval (by rfl) ha1 hM) ?_
  refine runs_seq_call_le hkC (vs := [a+2,I.m]) (two_call_check_args (by rfl) (by rfl) ha2 (by omega)) (by wram_words) ?_ ?_
  · refine ⟨a+2,rfl,hedge,?_,h8,?_⟩
    · change a+2+8*I.m<2^w
      rw [hencode] at hend; omega
    · intro x hx
      exact (hsourceWords x (instance_edges_word_mem I hx)).trans hGH
  · intro capFlag memC posC hpostC
    obtain ⟨hmemC,hcapFlag⟩ := hpostC
    change memC=mem at hmemC
    subst memC
    change capFlag=(if ∀ e∈I.edges,e.lower≤e.upper then 1 else 0) at hcapFlag
    wram_step
    · have hcap : ¬∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper := by
        intro hc
        have hL := (instance_capacity_order_iff I).mp hc
        rw [ite_eq_left hL] at hcapFlag
        omega
      have hmodel : r.value=none := by
        dsimp only [r]
        unfold FlowReduction.reduceMeasured
        rw [ite_eq_right hcap]
      refine runs_seq_call_le hkN (vs := [heap]) (by eval_expr) (by wram_words)
        ⟨⟨heap,rfl⟩,hz,by change heap+3<2^w; omega⟩ ?_
      intro out memN posN hpostN
      obtain ⟨⟨_,_,hframeN,hzN,_⟩,hout,hanswer⟩ := hpostN
      change out=heap+3 at hout
      change (∀ x<heap,memN x=mem x) at hframeN
      change ZeroFrom memN out at hzN
      have how : out<2^w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change heap≤out ∧ out≤heap+4*region ∧ ScalingAnswerAt memN (out-2) out (scalingAnswerWords r.value) ∧
          ZeroFrom memN out ∧ ∀ x<heap,memN x=mem x
        rw [hmodel]
        exact ⟨by omega,by omega,hanswer,hzN,hframeN⟩
      · simp only [capacityCheckContract,infeasibleResultContract,heapContract,argsSize_cons,argsSize_nil,
          Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        change _≤200*I.m+500+(if ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper then _ else 0)
        rw [ite_eq_right hcap]
        change _≤200*I.m+500
        have hmLen : I.edges.length=I.m := rfl
        rw [hmLen]
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
      have hFspace : feasibilityPhaseSpace I hv C U≤region :=
        feasibilityPhaseSpace_le_source_capacity solver entry T hproc I hv C U hC hcapList hd hlList huList
      obtain ⟨hwF,hpreF⟩ := feasibilityPhase_pre_of_source_space solver entry T hproc I hv C U a heap mem
        hC hcapList hd hlList huList hat hend hz (by change heap+region<2^w; omega)
      refine runs_seq_call_le hkF (vs := [a,C,U,heap]) (by eval_expr) hwF hpreF ?_
      intro firstEnd memF posF hpostF
      obtain ⟨hfirstLo,hfirstHi,gflow,hflowEnd,hflow,hheader,hgraph,hzF,hframeF⟩ := hpostF
      change heap+2+5*I.m≤firstEnd at hfirstLo
      change firstEnd≤heap+feasibilityPhaseSpace I hv C U at hfirstHi
      change gflow+P.m≤firstEnd at hflowEnd
      change ListAt memF gflow (List.ofFn (fun e => (g e).toNat)) at hflow
      change ListAt memF (firstEnd-3) [flag,gflow,heap] at hheader
      change ListAt memF heap (FlowReduction.shiftedGraph I hv).solverWords at hgraph
      change (∀ x<heap,memF x=mem x) at hframeF
      have hfword : firstEnd<2^w := by omega
      have hheaderPtr : firstEnd-3<2^w := by omega
      have hheader1 : firstEnd-3+1<2^w := by rw [hencode] at hend; omega
      have hheader2 : firstEnd-3+2<2^w := by rw [hencode] at hend; omega
      have hflagCell : memF (firstEnd-3)=flag := by
        have hc : memF (firstEnd-3+0)=flag := hheader 0 (by change 0<3; omega)
        simpa only [Nat.add_zero] using hc
      have hflowCell : memF (firstEnd-3+1)=gflow := hheader 1 (by change 1<3; omega)
      have hgraphCell : memF (firstEnd-3+2)=heap := hheader 2 (by change 2<3; omega)
      have hptrWord : gflow<2^w := by omega
      refine runs_seq_assign_le (v := firstEnd-3) (two_call_header_eval (by rfl) hfword (by omega)) ?_
      refine runs_seq_assign_le (v := flag) (two_call_flag_eval (by rfl) hheaderPtr hflagCell) ?_
      wram_step
      · have hbad : ¬good := by
          intro hg
          have hf : flag=1 := by simp only [flag,hg,↓reduceIte]
          omega
        have hmodel : r.value=none := by
          dsimp only [r]
          unfold FlowReduction.reduceMeasured
          rw [ite_eq_left hcap]
          change ((if good then _ else _) : CallResult (Option (Fin I.m → ℤ))).value=none
          rw [ite_eq_right hbad]
        refine runs_seq_call_le hkN (vs := [firstEnd]) (by eval_expr) (by wram_words)
          ⟨⟨firstEnd,rfl⟩,hzF,by change firstEnd+3<2^w; omega⟩ ?_
        intro out memN posN hpostN
        obtain ⟨⟨_,_,hframeN,hzN,_⟩,hout,hanswer⟩ := hpostN
        change out=firstEnd+3 at hout
        change (∀ x<firstEnd,memN x=memF x) at hframeN
        change ZeroFrom memN out at hzN
        have how : out<2^w := by omega
        refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
        · change heap≤out ∧ out≤heap+4*region ∧ ScalingAnswerAt memN (out-2) out (scalingAnswerWords r.value) ∧
            ZeroFrom memN out ∧ ∀ x<heap,memN x=mem x
          rw [hmodel]
          refine ⟨by omega,by omega,hanswer,hzN,?_⟩
          intro x hx
          exact (hframeN x (by omega)).trans (hframeF x hx)
        · simp only [capacityCheckContract,infeasibleResultContract,heapContract,argsSize_cons,argsSize_nil,
            Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
          change _≤200*I.m+500+(if ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper then F+(if good then _ else 50) else 0)
          rw [ite_eq_left hcap,ite_eq_right hbad,hFCost]
          have hmLen : I.edges.length=I.m := rfl
          rw [hmLen]
          omega
      · have hgood : good := by
          by_contra hn
          have hf : flag=0 := by simp only [flag,hn,↓reduceIte]
          exact hcond hf
        have hmodel : r.value=some result := by
          dsimp only [r]
          unfold FlowReduction.reduceMeasured
          rw [ite_eq_left hcap]
          change ((if good then _ else _) : CallResult (Option (Fin I.m → ℤ))).value=some result
          rw [ite_eq_left hgood]
        have hinputF := hat.of_agree_below hend hframeF
        have hprefix := unsignedFlow_castAdd_prefix g hflow
        change ListAt memF gflow (List.ofFn (fun e => (f e).toNat)) at hprefix
        have hgraphEnd : heap+(FlowReduction.shiftedGraph I hv).solverWords.length≤firstEnd := by
          rw [(FlowReduction.shiftedGraph I hv).solverWords_length]
          change heap+(2+5*I.m)≤firstEnd
          omega
        have hprefixEnd : gflow+I.m≤firstEnd := by change gflow+(I.m+(I.n+I.n))≤firstEnd at hflowEnd; omega
        obtain ⟨hwO,hpreO⟩ := residualOptimization_pre_of_source_space solver entry T hproc I hv f C U
          a heap gflow firstEnd memF hfBounds hcost hl hu hinputF hgraph hprefix
          (by omega) hgraphEnd hprefixEnd hzF (by change firstEnd+region<2^w; omega)
        refine runs_seq_assign_le (v := gflow) (two_call_flow_eval (by rfl) hheader1 (by omega) hflowCell) ?_
        refine runs_seq_assign_le (v := heap) (two_call_graph_eval (by rfl) hheader2 (by omega) hgraphCell) ?_
        refine runs_seq_call_le hkO (vs := [a,heap,gflow,C,U,firstEnd]) (by eval_expr) hwO hpreO ?_
        intro secondEnd memO posO hpostO
        obtain ⟨hsecondLo,hsecondHi,hresult,hzO,hframeO⟩ := hpostO
        change firstEnd≤secondEnd at hsecondLo
        change secondEnd≤firstEnd+residualOptimizationSpace I hv f C U at hsecondHi
        change SignedTableAt memO (secondEnd-2*I.m) result at hresult
        change (∀ x<firstEnd,memO x=memF x) at hframeO
        have hsword : secondEnd<2^w := by omega
        have hresultPtr : secondEnd-2*I.m<2^w := by omega
        have hresultEnd : secondEnd-2*I.m+2*I.m≤secondEnd := by omega
        refine runs_seq_call_le hkS (vs := [secondEnd-2*I.m,I.m,secondEnd])
          (two_call_success_args (by rfl) (by rfl) hsword (by omega) h2m) (by wram_words)
          ⟨⟨secondEnd-2*I.m,secondEnd,rfl,hresult,hresultEnd,by omega⟩,hzO,
            by change secondEnd+(3+2*I.m)<2^w; omega⟩ ?_
        intro out memS posS hpostS
        obtain ⟨⟨_,_,hframeS,hzS,_⟩,hout,hanswer⟩ := hpostS
        change out=secondEnd+3+2*I.m at hout
        change (∀ x<secondEnd,memS x=memO x) at hframeS
        change ZeroFrom memS out at hzS
        have how : out<2^w := by omega
        refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
        · change heap≤out ∧ out≤heap+4*region ∧ ScalingAnswerAt memS (out-2) out (scalingAnswerWords r.value) ∧
            ZeroFrom memS out ∧ ∀ x<heap,memS x=mem x
          rw [hmodel]
          refine ⟨by omega,by omega,hanswer,hzS,?_⟩
          intro x hx
          exact (hframeS x (by omega)).trans ((hframeO x (by omega)).trans (hframeF x hx))
        · simp only [capacityCheckContract,flowResultContract,heapContract,argsSize_cons,argsSize_nil,
            Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
          change _≤200*I.m+500+(if ∀ e : Fin I.m,(I.edge e).lower≤(I.edge e).upper then F+(if good then O+40*I.m+150 else 50) else 0)
          rw [ite_eq_left hcap,ite_eq_left hgood,hFCost,hOCost]
          have hmLen : I.edges.length=I.m := rfl
          rw [hmLen]
          omega

end MinCostFlow.Scaling.Machine
