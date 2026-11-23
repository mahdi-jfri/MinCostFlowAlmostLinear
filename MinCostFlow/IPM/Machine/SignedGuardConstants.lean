module

public import MinCostFlow.IPM.Machine.GuardConstants
public import MinCostFlow.Num.Negate
import MinCostFlow.Num.IPM.FixedPointFacts
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Constructing both signed coefficient range endpoints

The existing constant writer produces the positive minimum, maximum
and stopping threshold. Negate the positive maximum into a fourth
block for the gradient guard. Its negation fits because the positive
source fits the same signed width. The old prefix and the first three
constant blocks survive this final call.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[R,L,P,heap]`. The blocks are minimum, maximum,
one quarter and negative maximum, in that order. -/
def signedGuardConstantsBody (constants neg : ℕ) : Stmt :=
  .call 4 constants [.reg 0,.reg 1,.reg 2,.reg 3] ;;
  .call 5 neg [.bin .add (.reg 3) (.reg 1),.reg 1,.reg 4] ;;
  .ret (.reg 5)

/-- The exact positive constants followed by one shared signed negation. -/
def signedGuardConstantsModule (b : ℕ) : List Stmt :=
  let neg := b+1+(guardConstantsModule (b+1)).length
  [signedGuardConstantsBody (b+1) neg] ++
    (guardConstantsModule (b+1) ++ Num.negateModule neg 4)

/-- Four exact fixed-point blocks, without any caller-supplied numeric
oracle or initialized signed endpoint. -/
def signedGuardConstantsContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ R L P heap,args=[R,L,P,heap] ∧ R≤P ∧ 2≤P ∧
      P+R+2≤4*L ∧ P+R<2^w)
    (fun args _ mem' =>
      ScalarAt mem' (heapArg args) 4 (args.getD 1 0) (args.getD 2 0) (1/(2:ℝ)^(args.getD 0 0)) ∧
      ScalarAt mem' (heapArg args+args.getD 1 0) 4 (args.getD 1 0) (args.getD 2 0) ((2:ℝ)^(args.getD 0 0)) ∧
      ScalarAt mem' (heapArg args+2*args.getD 1 0) 4 (args.getD 1 0) (args.getD 2 0) (1/4) ∧
      ScalarAt mem' (heapArg args+3*args.getD 1 0) 4 (args.getD 1 0) (args.getD 2 0) (-(2:ℝ)^(args.getD 0 0)))
    (fun args _ => 36*args.getD 1 0+450) (fun args _ => 4*args.getD 1 0)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+4*args.getD 1 0}

/-- The signed endpoint construction uses no random statements. -/
theorem signedGuardConstantsModule_noRand (b : ℕ) :
    ∀ body∈signedGuardConstantsModule b,body.NoRand := by
  intro body hb
  simp only [signedGuardConstantsModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hc | hn
  · simp [signedGuardConstantsBody,Stmt.NoRand]
  · exact guardConstantsModule_noRand _ _ hc
  · exact Num.negateModule_noRand _ _ _ hn

private theorem scalar_frozen {mem mem' : ℕ → ℕ} {a L P heap : ℕ} {x : ℝ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap)
    (hx : ScalarAt mem a 4 L P x) : ScalarAt mem' a 4 L P x :=
  ⟨Num.IPM.valid_frozen hf ha hx.1,(Num.IPM.fixVal_frozen hf ha).trans hx.2⟩

/-- The actual positive-constant and negation calls construct all four
blocks with exact allocation and explicit operation cost. -/
theorem signedGuardConstants_meetsContract {w b : ℕ} {p : Program}
    (hw : 16<2^w) (hp : p.HasAt b (signedGuardConstantsModule b)) :
    MeetsContract w p b (signedGuardConstantsContract w) := by
  have ht := Num.hasAt_append_right hp
  have hc := guardConstants_meetsContract hw (Num.hasAt_append_left ht)
  have hn := Num.negate_meetsContract (by omega : 1<2^w) (show Num.base 4<2^w by simpa [Num.base] using hw)
    (Num.hasAt_append_right ht)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨R,L,P,heap,rfl,hRP,hP,hwidth,hword⟩,hz,hspace⟩ := hpre
  change heap+4*L<2^w at hspace
  have hRW := hwords R (by simp)
  have hLW := hwords L (by simp)
  have hPW := hwords P (by simp)
  have hhW := hwords heap (by simp)
  apply runs_start_le
  unfold signedGuardConstantsBody
  refine runs_seq_call_le hc (vs:=[R,L,P,heap]) (by eval_expr) hwords
    ⟨⟨R,L,P,heap,rfl,hRP,hP,hwidth,hword⟩,hz,by change heap+3*L<2^w; omega⟩ ?_
  intro v0 mem0 pos0 hout0
  obtain ⟨⟨_,_,hframe0,hzero0,hdata⟩,hv0⟩ := hout0
  change v0=heap+3*L at hv0
  change ∀ z<heap,mem0 z=mem z at hframe0
  change ScalarAt mem0 heap 4 L P (1/(2:ℝ)^R) ∧
    ScalarAt mem0 (heap+L) 4 L P ((2:ℝ)^R) ∧
    ScalarAt mem0 (heap+2*L) 4 L P (1/4) at hdata
  have hnonneg : 0≤Num.intVal mem0 (heap+L) 4 L := by
    have hr : (0:ℝ)<Num.fixVal mem0 (heap+L) 4 L P := by rw [hdata.2.1.2]; positivity
    unfold Num.fixVal at hr
    have hh := (div_pos_iff_of_pos_right (by positivity : (0:ℝ)<2^P)).mp hr
    exact_mod_cast hh.le
  have hfit := Num.intVal_fits hdata.2.1.1
  have hcap : (0:ℤ)<Num.capacity 4 L := by exact_mod_cast Num.capacity_pos 4 L
  have hnegFit : Num.Fits 4 L (-Num.intVal mem0 (heap+L) 4 L) := by
    unfold Num.Fits at hfit ⊢
    omega
  have hvW : v0<2^w := by omega
  have hmaxW : heap+L<2^w := by omega
  refine runs_seq_call_le hn (vs:=[heap+L,L,v0]) (by eval_expr) (by wram_words)
    ⟨heap+L,L,v0,rfl,⟨⟨heap+L,L,1,v0,rfl,by omega,by decide,hdata.2.1.1⟩,
      hzero0,by change v0+L<2^w; omega⟩⟩ ?_
  intro v mem' pos' hout
  obtain ⟨hv,_,_,hframe,hzero,hlist⟩ := hout
  change v=v0+L at hv
  change ∀ z<v0,mem' z=mem0 z at hframe
  change ListAt mem' v0 (Num.digits 4 L (Num.capacity 4 L-1-Num.unsignedVal mem0 (heap+L) 4 L+1)) at hlist
  obtain ⟨hvalid,hvalue⟩ := Num.negateCarry_value_one hdata.2.1.1 hlist
  rw [Num.wrap_of_fits hnegFit] at hvalue
  have hnegative : ScalarAt mem' v0 4 L P (-(2:ℝ)^R) := by
    refine ⟨hvalid,?_⟩
    unfold Num.fixVal
    rw [hvalue,Int.cast_neg,neg_div]
    exact congrArg Neg.neg hdata.2.1.2
  have hmin := scalar_frozen hframe (show heap+L≤v0 by omega) hdata.1
  have hmax := scalar_frozen hframe (show heap+L+L≤v0 by omega) hdata.2.1
  have hquarter := scalar_frozen hframe (show heap+2*L+L≤v0 by omega) hdata.2.2
  have hvWord : v<2^w := by omega
  refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
  · change (heap≤v ∧ v≤heap+4*L ∧ (∀ z<heap,mem' z=mem z) ∧ ZeroFrom mem' v ∧
      ScalarAt mem' heap 4 L P (1/(2:ℝ)^R) ∧ ScalarAt mem' (heap+L) 4 L P ((2:ℝ)^R) ∧
      ScalarAt mem' (heap+2*L) 4 L P (1/4) ∧ ScalarAt mem' (heap+3*L) 4 L P (-(2:ℝ)^R)) ∧ v=heap+4*L
    refine ⟨⟨by omega,by omega,?_,hzero,hmin,hmax,hquarter,?_⟩,by omega⟩
    · intro z hz0
      exact (hframe z (by omega)).trans (hframe0 z hz0)
    · simpa only [hv0] using hnegative
  · simp only [signedGuardConstantsContract,guardConstantsContract,heapContract,
      Num.negateContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,
      Expr.size_bin,argsSize_cons,argsSize_nil]
    omega

end MinCostFlow.IPM.Machine
