module

public import MinCostFlow.Num.IPM.GradientArrayLoop
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Allocating the IPM gradient vector

Reserve consecutive output blocks and one guard block, then evaluate all
edges with the shared residual and alpha. The procedure preserves the old
heap prefix. Its error statement specializes to the IPM's gradient tolerance.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[m,cost,residual,lower,flow,upper,alpha,one,L,P,E,heap]`. -/
def gradientArrayBody (loop : ℕ) : Stmt :=
  .call 12 loop [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 0,.reg 8,.reg 9,.reg 10,.reg 11,
    .bin .add (.reg 11) (.bin .mul (.bin .add (.reg 0) (.const 1)) (.reg 8))] ;;
  .ret (.reg 12)

/-- The allocating entry and its closed gradient scan. -/
def gradientArrayModule (b h : ℕ) : List Stmt :=
  [gradientArrayBody (b+1)] ++ gradientArrayLoopModule (b+1) h

/-- Allocation for the output vector, guard block, and scalar workspaces. -/
def gradientArraySpace (m L P E : ℕ) := (m+1)*L+m*gradientSpace L P E

/-- Explicit cost for the whole gradient vector. -/
def gradientArrayCost (m L P E : ℕ) := m*(gradientCost L P E+17*L+120)+70

/-- Output edge `i` is at `heap+iL`. Uniform precision, residual range,
and coefficient conditions are those of the scalar gradient procedure. -/
def gradientArrayContract (w h q K : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ m c r lo f up a one L P E heap,args=[m,c,r,lo,f,up,a,one,L,P,E,heap] ∧ h∣P ∧
      q+4*E+42≤P ∧ P+K+4*E+30≤h*L ∧ 2*P+9<2^w ∧ 20*m<2^w ∧ 20*m≤2^K ∧
      c+m*L≤heap ∧ r+L≤heap ∧ lo+m*L≤heap ∧ f+m*L≤heap ∧ up+m*L≤heap ∧ a+L≤heap ∧ one+L≤heap ∧
      Valid mem r h L ∧ 1/(2:ℝ)^E≤fixVal mem r h L P ∧ fixVal mem r h L P≤(2:ℝ)^E ∧
      (∀i<m,EdgeData mem (lo+i*L) (f+i*L) (up+i*L) a one h L P E ∧ Valid mem (c+i*L) h L ∧
        |20*(m:ℤ)*intVal mem (c+i*L) h L|≤(2:ℤ)^K))
    (fun _ _ _ => True)
    (fun args _ => gradientArrayCost (args.getD 0 0) (args.getD 8 0) (args.getD 9 0) (args.getD 10 0))
    (fun args _ => gradientArraySpace (args.getD 0 0) (args.getD 8 0) (args.getD 9 0) (args.getD 10 0))
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧
      (∀i<args.getD 0 0,Valid mem' (heapArg args+i*args.getD 8 0) h (args.getD 8 0) ∧
        |fixVal mem' (heapArg args+i*args.getD 8 0) h (args.getD 8 0) (args.getD 9 0)-
          arrayGradient mem (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 3 0)
            (args.getD 4 0) (args.getD 5 0) (args.getD 6 0) h (args.getD 8 0) (args.getD 9 0) i|≤
          (1/(2:ℝ)^q)*arrayLength mem (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) (args.getD 6 0)
            h (args.getD 8 0) (args.getD 9 0) i)}

/-- Gradient-vector evaluation is deterministic. -/
theorem gradientArrayModule_noRand (b h : ℕ) : ∀ s∈gradientArrayModule b h,s.NoRand := by
  intro s hs
  simp only [gradientArrayModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hg
  · simp [gradientArrayBody,Stmt.NoRand]
  · exact gradientArrayLoopModule_noRand _ _ _ hg

set_option maxRecDepth 16384 in
/-- The whole gradient array satisfies the coordinatewise tolerance,
preserving source memory and the fresh suffix above its returned pointer. -/
theorem gradientArray_meetsContract {w h b q K : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (gradientArrayModule b h)) :
    MeetsContract w p b (gradientArrayContract w h q K) := by
  have hg := hasAt_append_right hp
  change p.HasAt (b+1) _ at hg
  have hgc := gradientArrayLoop_meetsContract (q:=q) (K:=K) hh hw hg
  have hw1 : 1<2^w := lt_of_lt_of_le (by decide : 1<2^1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨m,c,r,lo,f,up,a,one,L,P,E,heap,rfl,hP,hprec,hwidth,hPw,hmw,hmB,hc,hr,hlo,hf,hup,ha,ho,hvr,hrl,hrh,hdata⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+gradientArraySpace m L P E<2^w at hbound
  have hmw' : m<2^w := hwords m (by simp)
  have hcw : c<2^w := hwords c (by simp)
  have hrw : r<2^w := hwords r (by simp)
  have hlow : lo<2^w := hwords lo (by simp)
  have hfw : f<2^w := hwords f (by simp)
  have hupw : up<2^w := hwords up (by simp)
  have haw : a<2^w := hwords a (by simp)
  have how : one<2^w := hwords one (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPword : P<2^w := hwords P (by simp)
  have hEw : E<2^w := hwords E (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have hm1w : m+1<2^w := by
    have hLpos : 0<L := by nlinarith only [hwidth]
    have ht : m+1≤(m+1)*L := Nat.le_mul_of_pos_right _ hLpos
    unfold gradientArraySpace at hbound
    omega
  have hreservew : (m+1)*L<2^w := by unfold gradientArraySpace at hbound; omega
  have hnextw : heap+(m+1)*L<2^w := by unfold gradientArraySpace at hbound; omega
  apply runs_start_le
  unfold gradientArrayBody
  refine runs_seq_call_le hgc (vs:=[m,c,r,lo,f,up,a,one,m,L,P,E,heap,heap+(m+1)*L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,rfl,hP,hprec,hwidth,hPw,hmw,hmB,hc,hr,hlo,hf,hup,ha,ho,
      le_rfl,hvr,hrl,hrh,hdata⟩,hz.mono (h':=heap+(m+1)*L) (by omega),
      by change heap+(m+1)*L+m*gradientSpace L P E<2^w; simpa only [gradientArraySpace,Nat.add_assoc] using hbound⟩
  · intro v mem₁ pos₁ hp₁
    rcases hp₁ with ⟨hl₁,hh₁,hz₁,fr₁,hvalues₁⟩
    change heap+(m+1)*L≤v at hl₁
    change v≤heap+(m+1)*L+m*gradientSpace L P E at hh₁
    change (∀z<heap,mem₁ z=mem z) at fr₁
    have hvw : v<2^w := by unfold gradientArraySpace at hbound; omega
    refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
    · change (heap≤v ∧ v≤heap+gradientArraySpace m L P E ∧ (∀z<heap,mem₁ z=mem z) ∧ ZeroFrom mem₁ v ∧ True) ∧ _
      exact ⟨⟨by omega,by unfold gradientArraySpace; omega,fr₁,hz₁,trivial⟩,hvalues₁⟩
    · simp only [gradientArrayContract,gradientArrayLoopContract,heapContract,gradientArrayCost,
        List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,argsSize_cons,argsSize_nil]
      omega

/-- Instance decoding equations identify the exact length formula. -/
theorem arrayLength_instance (I : Instance) (f : Fin I.m→ℝ) (e : Fin I.m)
    {lo fp up ap h L P : ℕ} {mem : ℕ→ℕ} {a : ℝ}
    (hlo : fixVal mem (lo+e.val*L) h L P=(I.edge e).lower)
    (hf : fixVal mem (fp+e.val*L) h L P=f e)
    (hup : fixVal mem (up+e.val*L) h L P=(I.edge e).upper)
    (ha : fixVal mem ap h L P=a) :
    arrayLength mem lo fp up ap h L P e.val=MinCostFlow.IPM.lengths I a f e := by
  simp only [arrayLength,hlo,hf,hup,ha]
  rfl

/-- Array decoding and an exact residual identify the IPM gradient. -/
theorem arrayGradient_instance (I : Instance) (f : Fin I.m→ℝ) (e : Fin I.m)
    {cp rp lo fp up ap h L P : ℕ} {mem : ℕ→ℕ} {a F : ℝ}
    (hc : intVal mem (cp+e.val*L) h L=(I.edge e).cost)
    (hr : fixVal mem rp h L P=I.cost f-F)
    (hlo : fixVal mem (lo+e.val*L) h L P=(I.edge e).lower)
    (hf : fixVal mem (fp+e.val*L) h L P=f e)
    (hup : fixVal mem (up+e.val*L) h L P=(I.edge e).upper)
    (ha : fixVal mem ap h L P=a) :
    arrayGradient mem I.m cp rp lo fp up ap h L P e.val=MinCostFlow.IPM.gradient I a F f e := by
  simp only [arrayGradient,hc,hr,hlo,hf,hup,ha]
  unfold MinCostFlow.IPM.gradient MinCostFlow.IPM.residual
  ring

/-- The gradient vector satisfies `GradientTolerance` directly, once the
input arrays decode the instance and its current flow. -/
theorem gradientArray_output (I : Instance) (f : Fin I.m→ℝ)
    {w h q K cp rp lo fp up ap one L P E heap v : ℕ} {mem mem' : ℕ→ℕ} {a F : ℝ}
    (hpre : (gradientArrayContract w h q K).pre [I.m,cp,rp,lo,fp,up,ap,one,L,P,E,heap] mem)
    (hout : (gradientArrayContract w h q K).post [I.m,cp,rp,lo,fp,up,ap,one,L,P,E,heap] mem v mem')
    (hc : ∀e : Fin I.m,intVal mem (cp+e.val*L) h L=(I.edge e).cost)
    (hr : fixVal mem rp h L P=I.cost f-F)
    (hlo : ∀e : Fin I.m,fixVal mem (lo+e.val*L) h L P=(I.edge e).lower)
    (hf : ∀e : Fin I.m,fixVal mem (fp+e.val*L) h L P=f e)
    (hup : ∀e : Fin I.m,fixVal mem (up+e.val*L) h L P=(I.edge e).upper)
    (ha : fixVal mem ap h L P=a) :
    MinCostFlow.IPM.GradientTolerance (MinCostFlow.IPM.lengths I a f)
      (fun e : Fin I.m => fixVal mem' (heap+e.val*L) h L P) (MinCostFlow.IPM.gradient I a F f) (1/(2:ℝ)^q) := by
  intro e
  have he := (hout.2 e.val e.isLt).2
  change |fixVal mem' (heap+e.val*L) h L P-arrayGradient mem I.m cp rp lo fp up ap h L P e.val|≤
    (1/(2:ℝ)^q)*arrayLength mem lo fp up ap h L P e.val at he
  rw [arrayGradient_instance I f e (hc e) hr (hlo e) (hf e) (hup e) ha,
      arrayLength_instance I f e (hlo e) (hf e) (hup e) ha] at he
  have hlenPos : 0<MinCostFlow.IPM.lengths I a f e := by
    have hdata0 : ∀i<I.m,EdgeData mem (lo+i*L) (fp+i*L) (up+i*L) ap one h L P E := by
      rcases hpre with ⟨⟨m',c',r',lo',f',up',a',one',L',P',E',heap',hargs,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hdata⟩,_,_⟩
      have heq : m'=I.m ∧ c'=cp ∧ r'=rp ∧ lo'=lo ∧ f'=fp ∧ up'=up ∧ a'=ap ∧ one'=one ∧ L'=L ∧ P'=P ∧ E'=E ∧ heap'=heap := by
        simpa only [List.cons.injEq,and_true] using hargs.symm
      rcases heq with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      intro i hi
      exact (hdata i hi).1
    have hd := hdata0 e.val e.isLt
    rcases hd with ⟨_,_,_,_,_,_,hu,_,hl,_,_,_⟩
    have huPos : 0<fixVal mem (up+e.val*L) h L P-fixVal mem (fp+e.val*L) h L P := lt_of_lt_of_le (by positivity) hu
    have hlPos : 0<fixVal mem (fp+e.val*L) h L P-fixVal mem (lo+e.val*L) h L P := lt_of_lt_of_le (by positivity) hl
    rw [← arrayLength_instance I f e (hlo e) (hf e) (hup e) ha]
    exact add_pos (Real.rpow_pos_of_pos huPos _) (Real.rpow_pos_of_pos hlPos _)
  rw [abs_div,abs_of_pos hlenPos]
  exact (div_le_iff₀ hlenPos).mpr he

end MinCostFlow.Num.IPM
