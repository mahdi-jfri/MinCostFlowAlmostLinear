module

public import MinCostFlow.Num.IPM.ArrayData
public import MinCostFlow.Num.IPM.Length
public import MinCostFlow.Num.IPM.WriteBlock
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Filling a consecutive array of approximate lengths

Evaluate one edge, copy its result into the reserved output array, and
advance all edge pointers by one block. One unused guard block separates
the output array from scratch memory. This makes source and destination
copies disjoint using the scalar procedure's existing heap contract.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[lower,flow,upper,alpha,one,n,L,P,E,out,heap]`. -/
def lengthArrayLoopBody (self length write : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 5) (.const 0)) (.ret (.reg 10))
    (.call 11 length [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 6,.reg 7,.reg 8,.reg 10] ;;
     .call 12 write [.bin .sub (.reg 11) (.reg 6),.reg 6,.reg 9] ;;
     .call 13 self [.bin .add (.reg 0) (.reg 6),.bin .add (.reg 1) (.reg 6),
       .bin .add (.reg 2) (.reg 6),.reg 3,.reg 4,.bin .sub (.reg 5) (.const 1),
       .reg 6,.reg 7,.reg 8,.bin .add (.reg 9) (.reg 6),.reg 11] ;;
     .ret (.reg 13))

/-- A scalar length evaluator and destination writer shared by every edge. -/
def lengthArrayLoopModule (b h : ℕ) : List Stmt :=
  [lengthArrayLoopBody b (b+1) (b+324)] ++ (lengthModule (b+1) h ++ writeBlockModule (b+324))

/-- Every edge obeys the scalar input ranges. Output and its guard block
are reserved below scratch memory. Cost is linear in the number of edges. -/
def lengthArrayLoopContract (w h q : ℕ) : Contract where
  pre args mem := (∃ lo f up a one n L P E out heap,args=[lo,f,up,a,one,n,L,P,E,out,heap] ∧ h∣P ∧
    q+4*E+41≤P ∧ P+4*E+20≤h*L ∧ 2*P+9<2^w ∧
    lo+n*L≤out ∧ f+n*L≤out ∧ up+n*L≤out ∧ a+L≤out ∧ one+L≤out ∧
    out+(n+1)*L≤heap ∧ (∀i<n,EdgeData mem (lo+i*L) (f+i*L) (up+i*L) a one h L P E)) ∧
    ZeroFrom mem (heapArg args) ∧
    heapArg args+args.getD 5 0*lengthSpace (args.getD 6 0) (args.getD 7 0) (args.getD 8 0)<2^w
  post args mem v mem' := heapArg args≤v ∧
    v≤heapArg args+args.getD 5 0*lengthSpace (args.getD 6 0) (args.getD 7 0) (args.getD 8 0) ∧
    ZeroFrom mem' v ∧ (∀z<args.getD 9 0,mem' z=mem z) ∧
    (∀i<args.getD 5 0,Valid mem' (args.getD 9 0+i*args.getD 6 0) h (args.getD 6 0) ∧
      MinCostFlow.IPM.ScalarApprox (1+1/(2:ℝ)^q)
        (fixVal mem' (args.getD 9 0+i*args.getD 6 0) h (args.getD 6 0) (args.getD 7 0))
        (arrayLength mem (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 3 0)
          h (args.getD 6 0) (args.getD 7 0) i))
  cost args _ := args.getD 5 0*(lengthCost (args.getD 6 0) (args.getD 7 0) (args.getD 8 0)+17*args.getD 6 0+100)+10

/-- The length array scan is deterministic. -/
theorem lengthArrayLoopModule_noRand (b h : ℕ) : ∀ s∈lengthArrayLoopModule b h,s.NoRand := by
  intro s hs
  simp only [lengthArrayLoopModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hl | hw
  · simp [lengthArrayLoopBody,Stmt.NoRand]
  · exact lengthModule_noRand _ _ _ hl
  · exact writeBlockModule_noRand _ _ hw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Every consecutive output block satisfies the scalar length approximation
for its original input edge, with the explicit scalar-call cost counted. -/
theorem lengthArrayLoop_meetsContract {w h b q : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (lengthArrayLoopModule b h)) :
    MeetsContract w p b (lengthArrayLoopContract w h q) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hl := hasAt_append_left ht
  have hwrite := hasAt_append_right ht
  change p.HasAt (b+324) _ at hwrite
  have hlc := length_meetsContract (q:=q) hh hw hl
  have hw1 : 1<2^w := lt_of_lt_of_le (by decide : 1<2^1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hwc := writeBlock_meetsContract (h:=h) hw1 hwrite
  apply meetsContract_of_rec (fun args _ => args.getD 5 0) hp.head
  intro t ih args mem pos ω hwords hpre ht
  rcases hpre with ⟨⟨lo,f,up,a,one,n,L,P,E,out,heap,rfl,hP,hprec,hwidth,hPw,hlo,hf,hup,ha,ho,hout,hdata⟩,hz,hbound⟩
  change n=t at ht
  subst t
  change ZeroFrom mem heap at hz
  change heap+n*lengthSpace L P E<2^w at hbound
  have hlow : lo<2^w := hwords lo (by simp)
  have hfw : f<2^w := hwords f (by simp)
  have hupw : up<2^w := hwords up (by simp)
  have haw : a<2^w := hwords a (by simp)
  have how : one<2^w := hwords one (by simp)
  have hnw : n<2^w := hwords n (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPword : P<2^w := hwords P (by simp)
  have hEw : E<2^w := hwords E (by simp)
  have houtw : out<2^w := hwords out (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  apply runs_start_le
  unfold lengthArrayLoopBody
  wram_step
  · have hn0 : n=0 := by simpa [startState] using hcond
    subst n
    refine runs_ret_le (v:=heap) (by eval_expr) ?_ ?_
    · change heap≤heap ∧ heap≤heap+0*lengthSpace L P E ∧ ZeroFrom mem heap ∧
        (∀z<out,mem z=mem z) ∧ (∀i<0,_)
      exact ⟨le_rfl,by omega,hz,fun _ _ => rfl,fun i hi => by omega⟩
    · simp only [lengthArrayLoopContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin]
      omega
  · have hn0 : n≠0 := by simpa [startState] using hcond
    obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    simp only [Nat.succ_eq_add_one] at *
    have hnl : L≤(N+1)*L := by rw [Nat.add_mul,one_mul]; omega
    have hspace : lengthSpace L P E≤(N+1)*lengthSpace L P E := by rw [Nat.add_mul,one_mul]; omega
    have hdata0 := hdata 0 (by omega)
    simp only [zero_mul,add_zero] at hdata0
    rcases hdata0 with ⟨hvl,hvf,hvu,hva,hvo,hone,hul,huh,hdl,hdh,ha0,ha1⟩
    refine runs_seq_call_le hlc (vs:=[lo,f,up,a,one,L,P,E,heap]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,_,_,_,_,_,_,rfl,hP,hprec,hwidth,hPw,by omega,by omega,by omega,by omega,by omega,
        hvl,hvf,hvu,hva,hvo,hone,hul,huh,hdl,hdh,ha0,ha1⟩,hz,
        by change heap+lengthSpace L P E<2^w; omega⟩
    · intro v₁ mem₁ pos₁ hp₁
      rcases hp₁ with ⟨⟨hl₁,hh₁,fr₁,hz₁,_⟩,hv₁,herr₁⟩
      change heap≤v₁ at hl₁
      change v₁≤heap+lengthSpace L P E at hh₁
      change (∀z<heap,mem₁ z=mem z) at fr₁
      change Valid mem₁ (v₁-L) h L at hv₁
      have herr0 : MinCostFlow.IPM.ScalarApprox (1+1/(2:ℝ)^q) (fixVal mem₁ (v₁-L) h L P)
          (arrayLength mem lo f up a h L P 0) := by
        simpa only [arrayLength,zero_mul,add_zero,List.getD_cons_zero,List.getD_cons_succ,startState] using herr₁
      have hLheap : L≤heap := by nlinarith only [hout,Nat.zero_le N]
      have hv₁w : v₁<2^w := by omega
      have hptr₁w : v₁-L<2^w := by omega
      have hguard : out+L+L≤heap := by nlinarith only [hout,Nat.zero_le N]
      have houtEnd : out+L<2^w := by omega
      have hdis : out+L≤v₁-L := by omega
      refine runs_seq_call_le hwc (vs:=[v₁-L,L,out]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨_,_,_,rfl,by omega,houtEnd,Or.inr hdis,hv₁⟩
      · intro vwrite mem₂ pos₂ hp₂
        rcases hp₂ with ⟨hew,fr₂,hlimbs,hvalid₂,hval₂⟩
        change (∀z,z<out ∨ out+L≤z → mem₂ z=mem₁ z) at fr₂
        change Valid mem₂ out h L at hvalid₂
        change intVal mem₂ out h L=intVal mem₁ (v₁-L) h L at hval₂
        have hfix₂ : fixVal mem₂ out h L P=fixVal mem₁ (v₁-L) h L P := by simp only [fixVal,hval₂]
        have hz₂ := zeroFrom_writeBlock fr₂ (show out+L≤v₁ by omega) hz₁
        have hframe : ∀z<out,mem₂ z=mem z := fun z hz => (fr₂ z (Or.inl hz)).trans (fr₁ z (by omega))
        have htailData : ∀i<N,EdgeData mem₂ (lo+L+i*L) (f+L+i*L) (up+L+i*L) a one h L P E := by
          intro i hi
          have hiL : (i+1)*L+L≤(N+1)*L := by
            have ht := Nat.mul_le_mul_right L (show i+2≤N+1 by omega)
            nlinarith only [ht]
          have hla : lo+L+i*L=lo+(i+1)*L := by ring
          have hfa : f+L+i*L=f+(i+1)*L := by ring
          have hua : up+L+i*L=up+(i+1)*L := by ring
          rw [hla,hfa,hua]
          exact edgeData_frozen hframe (by omega) (by omega) (by omega) ha ho (hdata (i+1) (by omega))
        have hrec := ih
        have hlow' : lo+L<2^w := by omega
        have hfw' : f+L<2^w := by omega
        have hupw' : up+L<2^w := by omega
        have hNw : N<2^w := by omega
        refine runs_seq_call_le hrec (vs:=[lo+L,f+L,up+L,a,one,N,L,P,E,out+L,v₁]) (by
          eval_expr
          conv_rhs => rw [← Nat.add_sub_cancel N 1]
          exact Expr.eval_sub (a:=.reg 5) (b:=.const 1) (x:=N+1) (y:=1) (by eval_expr) (by eval_expr) hnw)
          (by wram_words) ?_ ?_
        · refine ⟨⟨⟨_,_,_,_,_,_,_,_,_,_,_,rfl,hP,hprec,hwidth,hPw,?_,?_,?_,by omega,by omega,?_,htailData⟩,
            hz₂,?_⟩,?_⟩
          · nlinarith only [hlo]
          · nlinarith only [hf]
          · nlinarith only [hup]
          · nlinarith only [hout,hl₁]
          · change v₁+N*lengthSpace L P E<2^w
            nlinarith only [hbound,hh₁]
          · change N<N+1; omega
        · intro v mem₃ pos₃ hp₃
          rcases hp₃ with ⟨hl₃,hh₃,hz₃,fr₃,hvalues₃⟩
          change v₁≤v at hl₃
          change v≤v₁+N*lengthSpace L P E at hh₃
          change (∀z<out+L,mem₃ z=mem₂ z) at fr₃
          have hvw : v<2^w := by nlinarith only [hbound,hh₁,hh₃]
          refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
          · change heap≤v ∧ v≤heap+(N+1)*lengthSpace L P E ∧ ZeroFrom mem₃ v ∧
              (∀z<out,mem₃ z=mem z) ∧
              (∀i<N+1,Valid mem₃ (out+i*L) h L ∧ MinCostFlow.IPM.ScalarApprox (1+1/(2:ℝ)^q)
                (fixVal mem₃ (out+i*L) h L P) (arrayLength mem lo f up a h L P i))
            refine ⟨by omega,by nlinarith only [hh₁,hh₃],hz₃,?_,?_⟩
            · intro z hz
              rw [fr₃ z (by omega),hframe z hz]
            · intro i hi
              cases i with
              | zero =>
                simp only [zero_mul,add_zero]
                refine ⟨valid_frozen fr₃ (by omega) hvalid₂,?_⟩
                rw [fixVal_frozen fr₃ (show out+L≤out+L by omega),hfix₂]
                exact herr0
              | succ i =>
                have hi' : i<N := by omega
                obtain ⟨hv,herr⟩ := hvalues₃ i hi'
                change Valid mem₃ (out+L+i*L) h L at hv
                change MinCostFlow.IPM.ScalarApprox (1+1/(2:ℝ)^q) (fixVal mem₃ (out+L+i*L) h L P)
                  (arrayLength mem₂ (lo+L) (f+L) (up+L) a h L P i) at herr
                have hiL : (i+1)*L+L≤(N+1)*L := by
                  have ht := Nat.mul_le_mul_right L (show i+2≤N+1 by omega)
                  nlinarith only [ht]
                have hh : lo+L+i*L+L≤out := by nlinarith only [hlo,hiL]
                have hhf : f+L+i*L+L≤out := by nlinarith only [hf,hiL]
                have hhu : up+L+i*L+L≤out := by nlinarith only [hup,hiL]
                rw [arrayLength_frozen hframe hh hhf hhu ha,arrayLength_shift] at herr
                have ho' : out+L+i*L=out+(i+1)*L := by ring
                simpa only [Nat.succ_eq_add_one,ho'] using (show Valid mem₃ (out+L+i*L) h L ∧
                  MinCostFlow.IPM.ScalarApprox (1+1/(2:ℝ)^q) (fixVal mem₃ (out+L+i*L) h L P)
                    (arrayLength mem lo f up a h L P (i+1)) from ⟨hv,herr⟩)
          · simp only [lengthArrayLoopContract,Contract.below,lengthContract,writeBlockContract,heapContract,
              List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,argsSize_cons,argsSize_nil]
            ring_nf
            omega

end MinCostFlow.Num.IPM
