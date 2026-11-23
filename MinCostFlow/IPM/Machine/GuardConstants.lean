module

public import MinCostFlow.IPM.Machine.DyadicBlock
public import MinCostFlow.IPM.Machine.PrecisionParameters
import MinCostFlow.Num.IPM.FixedPointFacts
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Exact constants for target-test range and stopping guards

The range guards use the selected endpoints `2^-R` and `2^R`.
The stopping guard uses one quarter. Each has a single numerator bit,
so three calls to the verified dyadic block writer construct all three
at the common precision. Reinterpreting the stored one at precision
`P+R` gives exactly `2^R` at precision `P`.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[R,L,P,heap]`. Write minimum, maximum and one quarter. -/
def guardConstantsBody (block : ℕ) : Stmt :=
  .call 4 block [.reg 0,.reg 1,.reg 2,.reg 3] ;;
  .call 5 block [.const 0,.reg 1,.bin .add (.reg 2) (.reg 0),.reg 4] ;;
  .call 6 block [.const 2,.reg 1,.reg 2,.reg 5] ;;
  .ret (.reg 6)

/-- All three constants share one dyadic block entry. -/
def guardConstantsModule (b : ℕ) : List Stmt := [guardConstantsBody (b+1)] ++ dyadicBlockModule

/-- Three exact shared-precision guard constants in three L-limb blocks. -/
def guardConstantsContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ R L P heap,args=[R,L,P,heap] ∧ R ≤ P ∧ 2 ≤ P ∧
      P+R+2 ≤ 4*L ∧ P+R < 2^w)
    (fun args _ mem' =>
      ScalarAt mem' (heapArg args) 4 (args.getD 1 0) (args.getD 2 0) (1/(2:ℝ)^(args.getD 0 0)) ∧
      ScalarAt mem' (heapArg args+args.getD 1 0) 4 (args.getD 1 0) (args.getD 2 0) ((2:ℝ)^(args.getD 0 0)) ∧
      ScalarAt mem' (heapArg args+2*args.getD 1 0) 4 (args.getD 1 0) (args.getD 2 0) (1/4))
    (fun _ _ => 350) (fun args _ => 3*args.getD 1 0)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+3*args.getD 1 0}

/-- Guard constants are constructed without random instructions. -/
theorem guardConstantsModule_noRand (b : ℕ) : ∀ body ∈ guardConstantsModule b,body.NoRand := by
  intro body hb
  simp only [guardConstantsModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [guardConstantsBody,Stmt.NoRand]
  · have he : body=dyadicBlockBody := by simpa [dyadicBlockModule] using hb
    subst body
    exact dyadicBlock_noRand

private theorem one_at_larger_precision {mem : ℕ → ℕ} {a L P R : ℕ}
    (hone : ScalarAt mem a 4 L (P+R) 1) : ScalarAt mem a 4 L P ((2:ℝ)^R) := by
  refine ⟨hone.1,?_⟩
  have he := hone.2
  unfold Num.fixVal at he ⊢
  have hn : (Num.intVal mem a 4 L:ℝ)=(2:ℝ)^(P+R) :=
    (div_eq_one_iff_eq (by positivity)).mp he
  rw [hn,pow_add,mul_div_cancel_left₀ _ (by positivity)]

private theorem scalar_frozen {mem mem' : ℕ → ℕ} {a L P heap : ℕ} {x : ℝ}
    (hf : ∀ z < heap,mem' z=mem z) (ha : a+L ≤ heap)
    (hx : ScalarAt mem a 4 L P x) : ScalarAt mem' a 4 L P x :=
  ⟨Num.IPM.valid_frozen hf ha hx.1,(Num.IPM.fixVal_frozen hf ha).trans hx.2⟩

/-- Exact guard constants are written with all arithmetic and calls
counted, source framing and the exact three-block allocation. -/
theorem guardConstants_meetsContract {w b : ℕ} {p : Program}
    (hw : 16 < 2^w) (hp : p.HasAt b (guardConstantsModule b)) :
    MeetsContract w p b (guardConstantsContract w) := by
  have hb : p.HasAt (b+1) dyadicBlockModule := Num.hasAt_append_right hp
  have hblock := dyadicBlock_meetsContract hw hb
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨R,L,P,heap,rfl,hRP,hP,hwidth,hword⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+3*L < 2^w at hspace
  have hRW : R < 2^w := hwords _ (by simp)
  have hLW : L < 2^w := hwords _ (by simp)
  have hPW : P < 2^w := hwords _ (by simp)
  have hhW : heap < 2^w := hwords _ (by simp)
  apply runs_start_le
  unfold guardConstantsBody
  refine runs_seq_call_le hblock (vs:=[R,L,P,heap]) (by eval_expr) (by wram_words)
    ⟨⟨R,L,P,heap,rfl,hRP,by omega⟩,hz,by change heap+L < 2^w; omega⟩ ?_
  intro v0 mem0 pos0 hp0
  obtain ⟨⟨_,_,hframe0,hfresh0,hmin⟩,hv0⟩ := hp0
  change v0=heap+L at hv0
  change ∀ z < heap,mem0 z=mem z at hframe0
  change ScalarAt mem0 heap 4 L P (1/(2:ℝ)^R) at hmin
  have hv0W : v0 < 2^w := by omega
  refine runs_seq_call_le hblock (vs:=[0,L,P+R,v0]) (by eval_expr) (by wram_words)
    ⟨⟨0,L,P+R,v0,rfl,by omega,hwidth⟩,hfresh0,by change v0+L < 2^w; omega⟩ ?_
  intro v1 mem1 pos1 hp1
  obtain ⟨⟨_,_,hframe1,hfresh1,hmax⟩,hv1⟩ := hp1
  change v1=v0+L at hv1
  change ∀ z < v0,mem1 z=mem0 z at hframe1
  change ScalarAt mem1 v0 4 L (P+R) (1/(2:ℝ)^0) at hmax
  have hmax' := one_at_larger_precision (R:=R) (by simpa using hmax)
  have hmin' := scalar_frozen hframe1 (show heap+L ≤ v0 by omega) hmin
  have hv1W : v1 < 2^w := by omega
  refine runs_seq_call_le hblock (vs:=[2,L,P,v1]) (by eval_expr) (by wram_words)
    ⟨⟨2,L,P,v1,rfl,hP,by omega⟩,hfresh1,by change v1+L < 2^w; omega⟩ ?_
  intro v2 mem2 pos2 hp2
  obtain ⟨⟨_,_,hframe2,hfresh2,hquarter⟩,hv2⟩ := hp2
  change v2=v1+L at hv2
  change ∀ z < v1,mem2 z=mem1 z at hframe2
  change ScalarAt mem2 v1 4 L P (1/(2:ℝ)^2) at hquarter
  have hv2W : v2 < 2^w := by omega
  refine runs_ret_le (v:=v2) (by eval_expr) ?_ ?_
  · change (heap ≤ v2 ∧ v2 ≤ heap+3*L ∧ (∀ z < heap,mem2 z=mem z) ∧
      ZeroFrom mem2 v2 ∧ ScalarAt mem2 heap 4 L P (1/(2:ℝ)^R) ∧
      ScalarAt mem2 (heap+L) 4 L P ((2:ℝ)^R) ∧ ScalarAt mem2 (heap+2*L) 4 L P (1/4)) ∧
      v2=heap+3*L
    refine ⟨⟨by omega,by omega,?_,hfresh2,?_,?_,?_⟩,by omega⟩
    · intro z hz
      exact (hframe2 z (by omega)).trans ((hframe1 z (by omega)).trans (hframe0 z hz))
    · exact scalar_frozen hframe2 (by omega) hmin'
    · simpa only [hv0] using scalar_frozen hframe2 (show v0+L ≤ v1 by omega) hmax'
    · simpa only [show v1=heap+2*L by omega,show (2:ℝ)^2=4 by norm_num] using hquarter
  · simp only [guardConstantsContract,dyadicBlockContract,heapContract,Expr.size_bin,Expr.size_const,Expr.size_reg,argsSize_cons,argsSize_nil]
    omega

/-- The selected parameters prove every numeric input condition of the
actual guard-constant program; only its real workspace is supplied. -/
theorem guardConstants_pre_of_chosen_precision (m U : ℕ) {w heap : ℕ} {mem : ℕ → ℕ}
    (hw : ipmParameterWordBits m U ≤ w) (hz : ZeroFrom mem heap)
    (hspace : heap+3*ipmLimbs m U < 2^w) :
    (guardConstantsContract w).pre [ipmRangeExponent m U,ipmLimbs m U,ipmPrecision m U,heap] mem := by
  have hm := ipm_precision_margins m U
  have hpw := (ipm_parameter_words_fit m U hw).2.2.2.2.1
  refine ⟨⟨ipmRangeExponent m U,ipmLimbs m U,ipmPrecision m U,heap,rfl,
    by omega,by omega,by omega,by omega⟩,hz,hspace⟩

/-- The widened format also meets the guard writer’s arithmetic precondition. -/
theorem guardConstants_pre_of_quality_precision (m U k : ℕ) {w heap : ℕ} {mem : ℕ → ℕ}
    (hw : ipmQualityParameterWordBits m U k ≤ w) (hz : ZeroFrom mem heap)
    (hspace : heap+3*ipmQualityLimbs m U k < 2^w) :
    (guardConstantsContract w).pre [ipmQualityRangeExponent m U k,ipmQualityLimbs m U k,ipmQualityPrecision m U k,heap] mem := by
  have hm := ipm_quality_precision_margins m U k
  have hpw := (ipm_quality_parameter_words_fit m U k hw).2.2.2.2.1
  refine ⟨⟨ipmQualityRangeExponent m U k,ipmQualityLimbs m U k,ipmQualityPrecision m U k,heap,rfl,
    by omega,by omega,by omega,by omega⟩,hz,hspace⟩

end MinCostFlow.IPM.Machine
