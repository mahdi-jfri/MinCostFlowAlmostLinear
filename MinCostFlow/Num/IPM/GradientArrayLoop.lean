module

public import MinCostFlow.Num.IPM.ArrayData
public import MinCostFlow.Num.IPM.Gradient
public import MinCostFlow.Num.IPM.WriteBlock
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Filling a consecutive array of approximate gradients

Each edge uses the same residual, alpha, and precision. Evaluate the scalar
gradient, write its result into one reserved output block, and advance all
edge arrays. A guard block separates output and scratch storage. The error
of every entry is measured against its original exact edge length.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[m,cost,residual,lower,flow,upper,alpha,one,n,L,P,E,out,heap]`. -/
def gradientArrayLoopBody (self gradient write : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 8) (.const 0)) (.ret (.reg 13))
    (.call 14 gradient [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 9,.reg 10,.reg 11,.reg 13] ;;
     .call 15 write [.bin .sub (.reg 14) (.reg 9),.reg 9,.reg 12] ;;
     .call 16 self [.reg 0,.bin .add (.reg 1) (.reg 9),.reg 2,
       .bin .add (.reg 3) (.reg 9),.bin .add (.reg 4) (.reg 9),.bin .add (.reg 5) (.reg 9),
       .reg 6,.reg 7,.bin .sub (.reg 8) (.const 1),.reg 9,.reg 10,.reg 11,
       .bin .add (.reg 12) (.reg 9),.reg 14] ;;
     .ret (.reg 16))

/-- Scalar gradient computation and array writes shared by every edge. -/
def gradientArrayLoopModule (b h : ℕ) : List Stmt :=
  [gradientArrayLoopBody b (b+1) (b+385)] ++ (gradientModule (b+1) h ++ writeBlockModule (b+385))

/-- Uniform scalar preconditions, a valid residual, and per-edge cost bounds.
Output and one guard block are reserved below the scratch heap. -/
def gradientArrayLoopContract (w h q K : ℕ) : Contract where
  pre args mem := (∃ m c r lo f up a one n L P E out heap,args=[m,c,r,lo,f,up,a,one,n,L,P,E,out,heap] ∧ h∣P ∧
    q+4*E+42≤P ∧ P+K+4*E+30≤h*L ∧ 2*P+9<2^w ∧ 20*m<2^w ∧ 20*m≤2^K ∧
    c+n*L≤out ∧ r+L≤out ∧ lo+n*L≤out ∧ f+n*L≤out ∧ up+n*L≤out ∧ a+L≤out ∧ one+L≤out ∧
    out+(n+1)*L≤heap ∧ Valid mem r h L ∧ 1/(2:ℝ)^E≤fixVal mem r h L P ∧ fixVal mem r h L P≤(2:ℝ)^E ∧
    (∀i<n,EdgeData mem (lo+i*L) (f+i*L) (up+i*L) a one h L P E ∧ Valid mem (c+i*L) h L ∧
      |20*(m:ℤ)*intVal mem (c+i*L) h L|≤(2:ℤ)^K)) ∧
    ZeroFrom mem (heapArg args) ∧
    heapArg args+args.getD 8 0*gradientSpace (args.getD 9 0) (args.getD 10 0) (args.getD 11 0)<2^w
  post args mem v mem' := heapArg args≤v ∧
    v≤heapArg args+args.getD 8 0*gradientSpace (args.getD 9 0) (args.getD 10 0) (args.getD 11 0) ∧
    ZeroFrom mem' v ∧ (∀z<args.getD 12 0,mem' z=mem z) ∧
    (∀i<args.getD 8 0,Valid mem' (args.getD 12 0+i*args.getD 9 0) h (args.getD 9 0) ∧
      |fixVal mem' (args.getD 12 0+i*args.getD 9 0) h (args.getD 9 0) (args.getD 10 0)-
        arrayGradient mem (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 3 0)
          (args.getD 4 0) (args.getD 5 0) (args.getD 6 0) h (args.getD 9 0) (args.getD 10 0) i|≤
        (1/(2:ℝ)^q)*arrayLength mem (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) (args.getD 6 0)
          h (args.getD 9 0) (args.getD 10 0) i)
  cost args _ := args.getD 8 0*(gradientCost (args.getD 9 0) (args.getD 10 0) (args.getD 11 0)+17*args.getD 9 0+120)+10

/-- Gradient-array evaluation is deterministic. -/
theorem gradientArrayLoopModule_noRand (b h : ℕ) : ∀ s∈gradientArrayLoopModule b h,s.NoRand := by
  intro s hs
  simp only [gradientArrayLoopModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hg | hw
  · simp [gradientArrayLoopBody,Stmt.NoRand]
  · exact gradientModule_noRand _ _ _ hg
  · exact writeBlockModule_noRand _ _ hw

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- Each output block meets the original edge's length-scaled tolerance.
The scalar calculation and copy costs are counted once per edge. -/
theorem gradientArrayLoop_meetsContract {w h b q K : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (gradientArrayLoopModule b h)) :
    MeetsContract w p b (gradientArrayLoopContract w h q K) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hg := hasAt_append_left ht
  have hwrite := hasAt_append_right ht
  change p.HasAt (b+385) _ at hwrite
  have hgc := gradient_meetsContract (q:=q) (K:=K) hh hw hg
  have hw1 : 1<2^w := lt_of_lt_of_le (by decide : 1<2^1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hwc := writeBlock_meetsContract (h:=h) hw1 hwrite
  apply meetsContract_of_rec (fun args _ => args.getD 8 0) hp.head
  intro t ih args mem pos ω hwords hpre ht
  rcases hpre with ⟨⟨m,c,r,lo,f,up,a,one,n,L,P,E,out,heap,rfl,hP,hprec,hwidth,hPw,hmw,hmB,hc,hr,hlo,hf,hup,ha,ho,hout,hvr,hrl,hrh,hdata⟩,hz,hbound⟩
  change n=t at ht
  subst t
  change ZeroFrom mem heap at hz
  change heap+n*gradientSpace L P E<2^w at hbound
  have hmw' : m<2^w := hwords m (by simp)
  have hcw : c<2^w := hwords c (by simp)
  have hrw : r<2^w := hwords r (by simp)
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
  unfold gradientArrayLoopBody
  wram_step
  · have hn0 : n=0 := by simpa [startState] using hcond
    subst n
    refine runs_ret_le (v:=heap) (by eval_expr) ?_ ?_
    · change heap≤heap ∧ heap≤heap+0*gradientSpace L P E ∧ ZeroFrom mem heap ∧
        (∀z<out,mem z=mem z) ∧ (∀i<0,_)
      exact ⟨le_rfl,by omega,hz,fun _ _ => rfl,fun i hi => by omega⟩
    · simp only [gradientArrayLoopContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin]
      omega
  · have hn0 : n≠0 := by simpa [startState] using hcond
    obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    simp only [Nat.succ_eq_add_one] at *
    have hnl : L≤(N+1)*L := by rw [Nat.add_mul,one_mul]; omega
    have hspace : gradientSpace L P E≤(N+1)*gradientSpace L P E := by rw [Nat.add_mul,one_mul]; omega
    have hdata0 := hdata 0 (by omega)
    simp only [zero_mul,add_zero] at hdata0
    rcases hdata0 with ⟨⟨hvl,hvf,hvu,hva,hvo,hone,hul,huh,hdl,hdh,ha0,ha1⟩,hvc,hcB⟩
    refine runs_seq_call_le hgc (vs:=[m,c,r,lo,f,up,a,one,L,P,E,heap]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,_,_,_,_,_,_,_,_,_,rfl,hP,hprec,hwidth,hPw,hmw,hmB,hcB,
        by omega,by omega,by omega,by omega,by omega,by omega,by omega,
        hvc,hvr,hvl,hvf,hvu,hva,hvo,hone,hrl,hrh,hul,huh,hdl,hdh,ha0,ha1⟩,hz,
        by change heap+gradientSpace L P E<2^w; omega⟩
    · intro v₁ mem₁ pos₁ hp₁
      rcases hp₁ with ⟨⟨hl₁,hh₁,fr₁,hz₁,_⟩,hv₁,herr₁⟩
      change heap≤v₁ at hl₁
      change v₁≤heap+gradientSpace L P E at hh₁
      change (∀z<heap,mem₁ z=mem z) at fr₁
      change Valid mem₁ (v₁-L) h L at hv₁
      have herr0 : |fixVal mem₁ (v₁-L) h L P-arrayGradient mem m c r lo f up a h L P 0|≤
          (1/(2:ℝ)^q)*arrayLength mem lo f up a h L P 0 := by
        simpa only [arrayGradient,arrayLength,zero_mul,add_zero,List.getD_cons_zero,List.getD_cons_succ,startState] using herr₁
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
        have htailData : ∀i<N,EdgeData mem₂ (lo+L+i*L) (f+L+i*L) (up+L+i*L) a one h L P E ∧
            Valid mem₂ (c+L+i*L) h L ∧ |20*(m:ℤ)*intVal mem₂ (c+L+i*L) h L|≤(2:ℤ)^K := by
          intro i hi
          have hiL : (i+1)*L+L≤(N+1)*L := by
            have ht := Nat.mul_le_mul_right L (show i+2≤N+1 by omega)
            nlinarith only [ht]
          have hca : c+L+i*L=c+(i+1)*L := by ring
          have hla : lo+L+i*L=lo+(i+1)*L := by ring
          have hfa : f+L+i*L=f+(i+1)*L := by ring
          have hua : up+L+i*L=up+(i+1)*L := by ring
          rw [hca,hla,hfa,hua]
          obtain ⟨hd,hcv,hcb⟩ := hdata (i+1) (by omega)
          refine ⟨edgeData_frozen hframe (by omega) (by omega) (by omega) ha ho hd,
            valid_frozen hframe (by omega) hcv,?_⟩
          rw [value_frozen (h:=h) hframe (show c+(i+1)*L+L≤out by omega)]
          exact hcb
        have hrfix := fixVal_frozen (h:=h) (P:=P) hframe hr
        have hrec := ih
        have hcw' : c+L<2^w := by omega
        have hlow' : lo+L<2^w := by omega
        have hfw' : f+L<2^w := by omega
        have hupw' : up+L<2^w := by omega
        have hNw : N<2^w := by omega
        refine runs_seq_call_le hrec (vs:=[m,c+L,r,lo+L,f+L,up+L,a,one,N,L,P,E,out+L,v₁]) (by
          eval_expr
          conv_rhs => rw [← Nat.add_sub_cancel N 1]
          exact Expr.eval_sub (a:=.reg 8) (b:=.const 1) (x:=N+1) (y:=1) (by eval_expr) (by eval_expr) hnw)
          (by wram_words) ?_ ?_
        · refine ⟨⟨⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,rfl,hP,hprec,hwidth,hPw,hmw,hmB,?_,by omega,?_,?_,?_,by omega,by omega,?_,
            valid_frozen hframe hr hvr,?_,?_,htailData⟩,hz₂,?_⟩,?_⟩
          · nlinarith only [hc]
          · nlinarith only [hlo]
          · nlinarith only [hf]
          · nlinarith only [hup]
          · nlinarith only [hout,hl₁]
          · rw [hrfix]; exact hrl
          · rw [hrfix]; exact hrh
          · change v₁+N*gradientSpace L P E<2^w
            nlinarith only [hbound,hh₁]
          · change N<N+1; omega
        · intro v mem₃ pos₃ hp₃
          rcases hp₃ with ⟨hl₃,hh₃,hz₃,fr₃,hvalues₃⟩
          change v₁≤v at hl₃
          change v≤v₁+N*gradientSpace L P E at hh₃
          change (∀z<out+L,mem₃ z=mem₂ z) at fr₃
          have hvw : v<2^w := by nlinarith only [hbound,hh₁,hh₃]
          refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
          · change heap≤v ∧ v≤heap+(N+1)*gradientSpace L P E ∧ ZeroFrom mem₃ v ∧
              (∀z<out,mem₃ z=mem z) ∧ (∀i<N+1,Valid mem₃ (out+i*L) h L ∧
                |fixVal mem₃ (out+i*L) h L P-arrayGradient mem m c r lo f up a h L P i|≤
                  (1/(2:ℝ)^q)*arrayLength mem lo f up a h L P i)
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
                obtain ⟨hv,herr⟩ := hvalues₃ i (show i<N by omega)
                change Valid mem₃ (out+L+i*L) h L at hv
                change |fixVal mem₃ (out+L+i*L) h L P-arrayGradient mem₂ m (c+L) r (lo+L) (f+L) (up+L) a h L P i|≤
                  (1/(2:ℝ)^q)*arrayLength mem₂ (lo+L) (f+L) (up+L) a h L P i at herr
                have hiL : (i+1)*L+L≤(N+1)*L := by
                  have ht := Nat.mul_le_mul_right L (show i+2≤N+1 by omega)
                  nlinarith only [ht]
                have hhc : c+L+i*L+L≤out := by nlinarith only [hc,hiL]
                have hhl : lo+L+i*L+L≤out := by nlinarith only [hlo,hiL]
                have hhf : f+L+i*L+L≤out := by nlinarith only [hf,hiL]
                have hhu : up+L+i*L+L≤out := by nlinarith only [hup,hiL]
                rw [arrayLength_frozen hframe hhl hhf hhu ha,arrayLength_shift,
                    arrayGradient_frozen hframe hhc hr hhl hhf hhu ha,arrayGradient_shift] at herr
                have ho' : out+L+i*L=out+(i+1)*L := by ring
                simpa only [Nat.succ_eq_add_one,ho'] using
                  (show Valid mem₃ (out+L+i*L) h L ∧
                    |fixVal mem₃ (out+L+i*L) h L P-arrayGradient mem m c r lo f up a h L P (i+1)|≤
                      (1/(2:ℝ)^q)*arrayLength mem lo f up a h L P (i+1) from ⟨hv,herr⟩)
          · simp only [gradientArrayLoopContract,Contract.below,gradientContract,writeBlockContract,heapContract,
              List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,argsSize_cons,argsSize_nil]
            ring_nf
            omega

end MinCostFlow.Num.IPM
