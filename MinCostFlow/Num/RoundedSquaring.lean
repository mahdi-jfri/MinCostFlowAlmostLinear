module

public import MinCostFlow.Num.SquaringIntegerFacts
public import MinCostFlow.Num.Copy
public import MinCostFlow.Num.FixedMultiply
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Verified repeated fixed-point squaring

Copy the initial value for the zero-step case. For a positive step count,
recursively compute the earlier result and apply fixed-point multiplication to
its square. An exact final-power bound ensures that no rounded numerator wraps.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Space for the initial copy and all quadratic multiplication workspaces. -/
def roundedSquaringSpace (L n : ℕ) : ℕ := n*(11*L+1)+L

/-- Arguments `[a,L,P,B,n,heap]`. -/
def roundedSquaringBody (self copy mul : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 4) (.const 0))
    (.call 6 copy [.reg 0,.reg 1,.reg 5] ;; .ret (.reg 6))
    (.call 6 self [.reg 0,.reg 1,.reg 2,.reg 3,.bin .sub (.reg 4) (.const 1),.reg 5] ;;
     .call 7 mul [.bin .sub (.reg 6) (.reg 1),.bin .sub (.reg 6) (.reg 1),
       .reg 1,.reg 2,.reg 6] ;;
     .ret (.reg 7))

/-- Squaring and its closed arithmetic dependencies. -/
def roundedSquaringModule (b h : ℕ) : List Stmt :=
  [roundedSquaringBody b (b+1) (b+2)] ++ (copyModule (b+1) ++ fixedMultiplyModule (b+2) h)

/-- The exact-power input bound is used only to ensure that every intermediate
fits. The output is the last `L` cells below the returned heap pointer. -/
def roundedSquaringContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a L P B n heap,args=[a,L,P,B,n,heap] ∧ h∣P ∧
      P+2*B+4≤h*L ∧ a+L≤heap ∧ Valid mem a h L ∧ (2:ℤ)^P≤ intVal mem a h L ∧
      (fixVal mem a h L P)^(2^n)≤(2:ℝ)^(2*B))
    (fun args mem mem' =>
      Valid mem' (heapArg args+roundedSquaringSpace (args.getD 1 0) (args.getD 4 0)-args.getD 1 0)
        h (args.getD 1 0) ∧
      intVal mem' (heapArg args+roundedSquaringSpace (args.getD 1 0) (args.getD 4 0)-args.getD 1 0)
        h (args.getD 1 0)=squaresInt (args.getD 2 0)
          (intVal mem (args.getD 0 0) h (args.getD 1 0)) (args.getD 4 0))
    (fun args _ => args.getD 4 0*(200*(args.getD 1 0)^2+500*args.getD 1 0+500)+17*args.getD 1 0+30)
    (fun args _ => roundedSquaringSpace (args.getD 1 0) (args.getD 4 0))
  { C with post := fun args mem v mem' =>
    v=heapArg args+roundedSquaringSpace (args.getD 1 0) (args.getD 4 0) ∧ C.post args mem v mem' }

/-- The repeated-squaring module contains no random statement. -/
theorem roundedSquaringModule_noRand (b h : ℕ) : ∀ s∈roundedSquaringModule b h,s.NoRand := by
  intro s hs
  simp only [roundedSquaringModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hc | hm
  · simp [roundedSquaringBody,Stmt.NoRand]
  · have he : s=copyBody := by simpa [copyModule] using hc
    subst s
    exact copyBody_noRand
  · exact fixedMultiplyModule_noRand _ _ _ hm

private theorem squaring_space_step (L n : ℕ) :
    roundedSquaringSpace L (n+1)=roundedSquaringSpace L n+(11*L+1) := by
  unfold roundedSquaringSpace
  ring

/-- Repeated squaring computes exactly the rounded integer recurrence within
the explicit polynomial resource bounds. -/
theorem roundedSquaring_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 2*h+2≤w) (hp : p.HasAt b (roundedSquaringModule b h)) :
    MeetsContract w p b (roundedSquaringContract w h) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hc := hasAt_append_left ht
  have hm := hasAt_append_right ht
  change p.HasAt (b+2) _ at hm
  have hb := base_lt_word hw
  have hw1 : 1<2^w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  have hw0 : w≠0 := by omega
  have hcC := copy_meetsContract (h:=h) hw1 hc
  have hmC := fixedMultiply_meetsContract hh hw hm
  apply meetsContract_of_rec (fun args _ => args.getD 4 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨⟨a,L,P,B,n,heap,rfl,hP,hwidth,ha,hva,hA,hpow⟩,hz,hbound⟩
  change n=k at hk
  subst k
  change ZeroFrom mem heap at hz
  change heap+roundedSquaringSpace L n<2^w at hbound
  change ((intVal mem a h L:ℝ)/(2:ℝ)^P)^(2^n)≤(2:ℝ)^(2*B) at hpow
  have haw : a<2^w := hwords a (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPw : P<2^w := hwords P (by simp)
  have hBw : B<2^w := hwords B (by simp)
  have hnw : n<2^w := hwords n (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  apply runs_start_le
  unfold roundedSquaringBody
  wram_step
  · have hn0 : n=0 := by simpa [startState] using hcond
    subst n
    have hend : heap+L<2^w := by simpa [roundedSquaringSpace] using hbound
    refine runs_seq_call_le hcC (vs:=[a,L,heap]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,rfl,ha,hva⟩,hz,hend⟩
    · intro v mem' pos' hp'
      rcases hp' with ⟨hv,_,_,hf,hz',_,hvalid,hvalue⟩
      change v=heap+L at hv
      change (∀ z<heap,mem' z=mem z) at hf
      change Valid mem' heap h L at hvalid
      change intVal mem' heap h L=intVal mem a h L at hvalue
      have hvw : v<2^w := by omega
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change v=heap+roundedSquaringSpace L 0 ∧ heap≤v ∧ v≤heap+roundedSquaringSpace L 0 ∧
          (∀ z<heap,mem' z=mem z) ∧ ZeroFrom mem' v ∧
          Valid mem' (heap+roundedSquaringSpace L 0-L) h L ∧
          intVal mem' (heap+roundedSquaringSpace L 0-L) h L=squaresInt P (intVal mem a h L) 0
        simp only [roundedSquaringSpace,zero_mul,zero_add,Nat.add_sub_cancel,squaresInt]
        exact ⟨hv,by omega,by omega,hf,hz',hvalid,hvalue⟩
      · simp only [roundedSquaringContract,copyContract,heapContract,List.getD_cons_zero,List.getD_cons_succ,
          Expr.size_reg,Expr.size_bin,Expr.size_const,argsSize_cons,argsSize_nil]
        omega
  · have hn0 : n≠0 := by simpa [startState] using hcond
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    rw [squaring_space_step] at hbound
    have hn' : n<2^w := by omega
    have hpR : (0:ℝ)<(2:ℝ)^P := by positivity
    have ha1 : 1≤(intVal mem a h L:ℝ)/(2:ℝ)^P := by
      apply (le_div_iff₀ hpR).mpr
      simpa only [one_mul] using (show (2:ℝ)^P≤(intVal mem a h L:ℝ) by exact_mod_cast hA)
    have hpow' : ((intVal mem a h L:ℝ)/(2:ℝ)^P)^(2^n)≤(2:ℝ)^(2*B) :=
      le_trans (pow_le_pow_right₀ ha1 (Nat.pow_le_pow_right (by decide) (show n≤n+1 by omega))) hpow
    have hrec : MeetsContract w p b
        ((roundedSquaringContract w h).below (fun args _ => args.getD 4 0) (n+1)) := ih
    refine runs_seq_call_le hrec (vs:=[a,L,P,B,n,heap])
      (by eval_expr <;> simp [Expr.eval,BinOp.eval,startState,hw0,hn']) (by wram_words) ?_ ?_
    · exact ⟨⟨⟨_,_,_,_,_,_,rfl,hP,hwidth,ha,hva,hA,hpow'⟩,
        hz,by change heap+roundedSquaringSpace L n<2^w; omega⟩,by change n<n+1; omega⟩
    · intro v₁ mem₁ pos₁ hp₁
      rcases hp₁ with ⟨hv₁,_,_,hf₁,hz₁,hvalid₁,hvalue₁⟩
      change v₁=heap+roundedSquaringSpace L n at hv₁
      change (∀ z<heap,mem₁ z=mem z) at hf₁
      change Valid mem₁ (heap+roundedSquaringSpace L n-L) h L at hvalid₁
      change intVal mem₁ (heap+roundedSquaringSpace L n-L) h L=squaresInt P (intVal mem a h L) n at hvalue₁
      rw [← hv₁] at hvalid₁ hvalue₁
      have hlow : L≤v₁ := by rw [hv₁]; unfold roundedSquaringSpace; omega
      have hv₁w : v₁<2^w := by omega
      have hptr₁w : v₁-L<2^w := by omega
      refine runs_seq_call_le hmC (vs:=[v₁-L,v₁-L,L,P,v₁]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨_,_,_,_,_,rfl,hP,by omega,by omega,hvalid₁,hvalid₁⟩,
          hz₁,by change v₁+(11*L+1)<2^w; omega⟩
      · intro v mem₂ pos₂ hp₂
        rcases hp₂ with ⟨hv,_,_,hf₂,hz₂,hvalid₂,hvalue₂⟩
        change v=v₁+(11*L+1) at hv
        change (∀ z<v₁,mem₂ z=mem₁ z) at hf₂
        change Valid mem₂ (v₁+10*L+1) h L at hvalid₂
        change intVal mem₂ (v₁+10*L+1) h L=
          wrap h L (intVal mem₁ (v₁-L) h L*intVal mem₁ (v₁-L) h L/(2:ℤ)^P) at hvalue₂
        rw [hvalue₁] at hvalue₂
        obtain ⟨hlo,hhi⟩ := squaresInt_bounds hA hpow
        have hscale0 : (0:ℤ)≤(2:ℤ)^P := by positivity
        have hfit : Fits h L (squaresInt P (intVal mem a h L) (n+1)) :=
          fits_exp_range hwidth (le_trans hscale0 hlo) hhi
        change intVal mem₂ (v₁+10*L+1) h L=wrap h L (squaresInt P (intVal mem a h L) (n+1)) at hvalue₂
        rw [wrap_of_fits hfit] at hvalue₂
        have hvw : v<2^w := by omega
        refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
        · change v=heap+roundedSquaringSpace L (n+1) ∧ heap≤v ∧ v≤heap+roundedSquaringSpace L (n+1) ∧
            (∀ z<heap,mem₂ z=mem z) ∧ ZeroFrom mem₂ v ∧
            Valid mem₂ (heap+roundedSquaringSpace L (n+1)-L) h L ∧
            intVal mem₂ (heap+roundedSquaringSpace L (n+1)-L) h L=squaresInt P (intVal mem a h L) (n+1)
          have he : v=heap+roundedSquaringSpace L (n+1) := by rw [squaring_space_step]; omega
          have hout : heap+roundedSquaringSpace L (n+1)-L=v₁+10*L+1 := by rw [← he]; omega
          refine ⟨he,by omega,by omega,?_,hz₂,?_,?_⟩
          · intro z hz
            exact (hf₂ z (by omega)).trans (hf₁ z hz)
          · rw [hout]; exact hvalid₂
          · rw [hout]; exact hvalue₂
        · simp only [roundedSquaringContract,Contract.below,fixedMultiplyContract,heapContract,
            List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,Expr.size_const,
            argsSize_cons,argsSize_nil,Nat.succ_eq_add_one,Nat.add_mul,Nat.mul_add]
          ring_nf
          omega

end MinCostFlow.Num
