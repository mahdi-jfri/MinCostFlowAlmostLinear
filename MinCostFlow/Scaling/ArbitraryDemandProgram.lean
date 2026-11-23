module

public import MinCostFlow.Scaling.ArbitraryDemandContract
import MinCostFlow.Scaling.GeneralScalingProgram
import MinCostFlow.Scaling.ScalingSourceWidth
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Executing the exact arbitrary-demand scaling model

The demand check uses the original capacity bound. On success its
pointwise bound implies the internal `(m+1)*U` demand bound required by
general scaling. The same budget covers the original lower and upper
capacities. The selected branch writes exactly the model's serialized
answer, with its shared pointer header and complete memory frames.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem arbitrary_count_eval {w a m : ℕ} {st : State}
    (h0 : st.regs 0=a) (ha : a+1<2^w) (hm : st.mem (a+1)=m) :
    Expr.eval w st (.load (.bin .add (.reg 0) (.const 1)))=some m := by eval_expr

private theorem arbitrary_check_args {w a U : ℕ} {st : State}
    (h0 : st.regs 0=a) (h2 : st.regs 2=U) : evalArgs w st [.reg 0,.reg 2]=some [a,U] := by eval_expr

private theorem arbitrary_capacity_eval {w m U : ℕ} {st : State}
    (h4 : st.regs 4=m) (h2 : st.regs 2=U) (h1 : 1<2^w) (hm : m+1<2^w) (hu : (m+1)*U<2^w) :
    Expr.eval w st (.bin .mul (.bin .add (.reg 4) (.const 1)) (.reg 2))=some ((m+1)*U) := by eval_expr

private theorem arbitrary_solve_args {w a C U heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h1 : st.regs 1=C) (h6 : st.regs 6=U) (h3 : st.regs 3=heap) :
    evalArgs w st [.reg 0,.reg 1,.reg 6,.reg 3]=some [a,C,U,heap] := by eval_expr

set_option maxRecDepth 4096 in
/-- The complete arbitrary-demand procedure writes exactly
`arbitraryDemandScalingModel`'s answer on every branch, with its declared
shared space, full frames, and selected-branch machine cost. -/
theorem arbitraryDemand_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (arbitraryDemandModule solver entry b)) (I : Instance) (hv : I.IsValid) (C U : ℕ) :
    MeetsContract w p b (arbitraryDemandContract w solver entry T hproc I hv C U) := by
  let solve := b+3
  let failure := solve+(generalScalingModule solver entry solve).length
  let U' := (I.m+1)*U
  let region := 2^wordSize 16384 (I.encode++[max C 1,U'])
  let r := FlowReduction.arbitraryDemandScalingModel (canonicalSolver solver entry T hproc) I hv C U
  let S := (generalScalingContract w solver entry T hproc I hv C U').cost [] (fun _ => 0)
  have ht : p.HasAt (b+1) (demandCheckModule (b+1) ++
      (generalScalingModule solver entry solve ++ infeasibleResultModule failure)) := hasAt_tail hp
  have hcheck := hasAt_append_left ht
  have htS : p.HasAt solve (generalScalingModule solver entry solve ++ infeasibleResultModule failure) := hasAt_append_right ht
  have hsolve := hasAt_append_left htS
  have hfailure : p.HasAt failure (infeasibleResultModule failure) := hasAt_append_right htS
  have hkS := generalScaling_meetsContract (w := w) hproc hdet hmono hsolve I hv C U'
  have hkN := infeasibleResult_meetsContract (w := w) hfailure
  have hG : 16≤region := sixteen_le_source_capacity 16384 _ (by decide)
  have hUle : U≤U' := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right U (show 1≤I.m+1 by omega)
  have hmU : I.m*U≤U' := Nat.mul_le_mul_right U (Nat.le_succ _)
  have hUguest : U'<region := lt_two_pow_wordSize_of_mem (by decide)
    (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hsourceWords : ∀ x∈I.encode,x<region := fun x hx =>
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_append_left _ hx)
  have hencode := instance_encode_length I hv
  have hSCost : ∀ args mem,(generalScalingContract w solver entry T hproc I hv C U').cost args mem=S := fun _ _ => rfl
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hat,hend,hcost,hl,hu,hz,hs⟩ := hpre
  change heap+10*region<2^w at hs
  have hGH : region<2^w := by omega
  have h8 : 8<2^w := by omega
  have hkC := demandCheck_meetsContract (w := w) h8 hcheck I hv
  have hh : heap<2^w := by omega
  have ha : a<2^w := by omega
  have ha1 : a+1<2^w := by rw [hencode] at hend; omega
  have hm1 : I.m+1<2^w := by rw [hencode] at hend; omega
  have hUw : U'<2^w := hUguest.trans hGH
  have hCword := hwords C (by simp)
  have hUword := hwords U (by simp)
  have hM := (instance_header_at I mem a hat).2
  apply runs_start_le
  unfold arbitraryDemandBody
  refine runs_seq_assign_le (v := I.m) (arbitrary_count_eval (by rfl) ha1 hM) ?_
  refine runs_seq_call_le hkC (vs := [a,U]) (arbitrary_check_args (by rfl) (by rfl)) (by wram_words) ?_ ?_
  · exact ⟨a,U,rfl,hat,by omega,hmU.trans_lt hUw,fun x hx => (hsourceWords x hx).trans hGH⟩
  · intro checkFlag memC posC hpostC
    obtain ⟨hmemC,hflag⟩ := hpostC
    change memC=mem at hmemC
    subst memC
    change checkFlag=(if FlowReduction.demandBoundCheck I U then 1 else 0) at hflag
    wram_step
    · have hcheckFalse : FlowReduction.demandBoundCheck I U=false := by
        by_contra hn
        have ht := Bool.eq_true_of_not_eq_false hn
        rw [ht] at hflag
        simp only [↓reduceIte] at hflag
        omega
      have hmodel : r.value=none := by
        unfold r FlowReduction.arbitraryDemandScalingModel
        simp only [hcheckFalse,Bool.false_eq_true,↓reduceIte]
      refine runs_seq_call_le hkN (vs := [heap]) (by eval_expr) (by wram_words)
        ⟨⟨heap,rfl⟩,hz,by change heap+3<2^w; omega⟩ ?_
      intro out memN posN hpostN
      obtain ⟨⟨_,_,hframeN,hzN,_⟩,hout,hanswer⟩ := hpostN
      change out=heap+3 at hout
      change (∀ x<heap,memN x=mem x) at hframeN
      change ZeroFrom memN out at hzN
      have how : out<2^w := by omega
      refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
      · change heap≤out ∧ out≤heap+10*region ∧ ScalingAnswerAt memN (out-2) out (scalingAnswerWords r.value) ∧
          ZeroFrom memN out ∧ ∀ x<heap,memN x=mem x
        rw [hmodel]
        exact ⟨by omega,by omega,hanswer,hzN,hframeN⟩
      · simp only [demandCheckContract,infeasibleResultContract,heapContract,argsSize_cons,argsSize_nil,
          Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        change _≤200*(I.n+1)+(if FlowReduction.demandBoundCheck I U then S else 50)
        simp only [hcheckFalse,Bool.false_eq_true,↓reduceIte]
        omega
    · have hcheckTrue : FlowReduction.demandBoundCheck I U=true := by
        by_contra hn
        have ht := Bool.eq_false_iff.mpr hn
        rw [ht] at hflag
        simp only [Bool.false_eq_true,↓reduceIte] at hflag
        exact hcond hflag
      have hd : ∀ v : Fin I.n,(I.d v).natAbs≤U' :=
        fun v => ((FlowReduction.demandBoundCheck_iff I U).mp hcheckTrue v).trans hmU
      have hl' : ∀ e,(I.edge e).lower.natAbs≤U' := fun e => (hl e).trans hUle
      have hu' : ∀ e,(I.edge e).upper.natAbs≤U' := fun e => (hu e).trans hUle
      have hmodel : r.value=(FlowReduction.generalScalingModel (canonicalSolver solver entry T hproc) I hv C U').value := by
        unfold r FlowReduction.arbitraryDemandScalingModel
        simp only [hcheckTrue,↓reduceIte]
        rfl
      refine runs_seq_assign_le (v := U') (arbitrary_capacity_eval (by rfl) (by rfl) (by omega) hm1 hUw) ?_
      refine runs_seq_call_le hkS (vs := [a,C,U',heap])
        (arbitrary_solve_args (by rfl) (by rfl) (by rfl) (by rfl)) (by wram_words) ?_ ?_
      · exact ⟨a,heap,rfl,hat,hend,hcost,hd,hl',hu',hz,
          by change heap+8*region<2^w; omega⟩
      · intro out memS posS hpostS
        obtain ⟨hlo,hhi,hanswer,hzS,hframeS⟩ := hpostS
        change heap≤out at hlo
        change out≤heap+8*region at hhi
        change (∀ x<heap,memS x=mem x) at hframeS
        change ZeroFrom memS out at hzS
        have how : out<2^w := by omega
        refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
        · change heap≤out ∧ out≤heap+10*region ∧ ScalingAnswerAt memS (out-2) out (scalingAnswerWords r.value) ∧
            ZeroFrom memS out ∧ ∀ x<heap,memS x=mem x
          rw [hmodel]
          exact ⟨hlo,by omega,hanswer,hzS,hframeS⟩
        · simp only [demandCheckContract,argsSize_cons,argsSize_nil,
            Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
          change _≤200*(I.n+1)+(if FlowReduction.demandBoundCheck I U then S else 50)
          simp only [hcheckTrue,↓reduceIte]
          rw [hSCost]
          omega

end MinCostFlow.Scaling.Machine
