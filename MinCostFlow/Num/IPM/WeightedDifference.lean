module

public import MinCostFlow.Num.IPM.Slacks
public import MinCostFlow.Num.IPM.Product
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Alpha times a difference of stored powers

The two barrier terms of Definition 4.2 of Chen et al. (page 24) have
the same factor alpha. Subtracting their stored powers first is exact.
Multiplication by alpha introduces just one output rounding.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[upperPower,lowerPower,alpha,L,P,heap]`. -/
def weightedDifferenceBody (sub mul : ℕ) : Stmt :=
  .call 6 sub [.reg 0,.reg 1,.reg 3,.reg 5] ;;
  .call 7 mul [.reg 2,.bin .sub (.reg 6) (.reg 3),.reg 3,.reg 4,.reg 6] ;;
  .ret (.reg 7)

/-- The difference is computed before one rounded product. -/
def weightedDifferenceModule (b h : ℕ) : List Stmt :=
  [weightedDifferenceBody (b+1) (b+6)] ++ (subtractModule (b+1) h ++ productModule (b+6) h)

/-- One rounding unit of error for alpha times the exact difference.
The returned value also has absolute size at most `2^(D+1)`. -/
def weightedDifferenceContract (w h D : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ u d a L P heap,args=[u,d,a,L,P,heap] ∧ h∣P ∧
      P+D+3≤h*L ∧ u+L≤heap ∧ d+L≤heap ∧ a+L≤heap ∧
      Valid mem u h L ∧ Valid mem d h L ∧ Valid mem a h L ∧
      0≤fixVal mem a h L P ∧ fixVal mem a h L P≤1 ∧
      |fixVal mem u h L P-fixVal mem d h L P|≤(2:ℝ)^D)
    (fun _ _ _ => True)
    (fun args _ => 152*(args.getD 3 0)^2+413*args.getD 3 0+400)
    (fun args _ => 13*args.getD 3 0+1)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧
      Valid mem' (v-args.getD 3 0) h (args.getD 3 0) ∧
      |fixVal mem' (v-args.getD 3 0) h (args.getD 3 0) (args.getD 4 0)-
        (fixVal mem (args.getD 2 0) h (args.getD 3 0) (args.getD 4 0)*
          (fixVal mem (args.getD 0 0) h (args.getD 3 0) (args.getD 4 0)-
            fixVal mem (args.getD 1 0) h (args.getD 3 0) (args.getD 4 0)))|≤1/(2:ℝ)^(args.getD 4 0) ∧
      |fixVal mem' (v-args.getD 3 0) h (args.getD 3 0) (args.getD 4 0)|≤(2:ℝ)^(D+1)}

/-- Weighted differences are deterministic. -/
theorem weightedDifferenceModule_noRand (b h : ℕ) : ∀ s∈weightedDifferenceModule b h,s.NoRand := by
  intro s hs
  simp only [weightedDifferenceModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hs | hp
  · simp [weightedDifferenceBody,Stmt.NoRand]
  · exact subtractModule_noRand _ _ _ hs
  · exact productModule_noRand _ _ _ hp

/-- The difference fits exactly. Alpha does not enlarge its absolute range,
so the final multiplication meets the rounded-product contract. -/
theorem weightedDifference_meetsContract {w h b D : ℕ} {p : Program}
    (hh : 0<h) (hw : 2*h+2≤w) (hp : p.HasAt b (weightedDifferenceModule b h)) :
    MeetsContract w p b (weightedDifferenceContract w h D) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hs := hasAt_append_left ht
  have hm := hasAt_append_right ht
  change p.HasAt (b+6) _ at hm
  have hsc := subtract_meetsContract hh hw hs
  have hmc := product_meetsContract (D:=D) hh hw hm
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨u,d,a,L,P,heap,rfl,hP,hwidth,hu,hd,ha,hvu,hvd,hva,ha0,ha1,hB⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+(13*L+1)<2^w at hbound
  have hfit : Fits h L (intVal mem u h L-intVal mem d h L) :=
    fits_of_scaled_bound (P:=P) (E:=D) (by omega) (by simpa only [scaled_sub,fixVal] using hB)
  have huw : u<2^w := hwords u (by simp)
  have hdw : d<2^w := hwords d (by simp)
  have haw : a<2^w := hwords a (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPw : P<2^w := hwords P (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  apply runs_start_le
  unfold weightedDifferenceBody
  refine runs_seq_call_le hsc (vs:=[u,d,L,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,rfl,hu,hd,hvu,hvd⟩,hz,by change heap+2*L<2^w; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨he₁,hl₁,hh₁,fr₁,hz₁,hv₁,hval₁⟩
    change v₁=heap+2*L at he₁
    change (∀ z<heap,mem₁ z=mem z) at fr₁
    change Valid mem₁ (heap+L) h L at hv₁
    change intVal mem₁ (heap+L) h L=wrap h L (intVal mem u h L-intVal mem d h L) at hval₁
    rw [wrap_of_fits hfit] at hval₁
    have hptr : v₁-L=heap+L := by omega
    have hdiff : fixVal mem₁ (v₁-L) h L P=fixVal mem u h L P-fixVal mem d h L P := by
      rw [hptr]
      simp only [fixVal,hval₁,scaled_sub]
    have hafix := fixVal_frozen (h:=h) (P:=P) fr₁ ha
    have hprod : |fixVal mem₁ a h L P*fixVal mem₁ (v₁-L) h L P|≤(2:ℝ)^D := by
      rw [hafix,hdiff,abs_mul,abs_of_nonneg ha0]
      exact (mul_le_of_le_one_left (abs_nonneg _) ha1).trans hB
    have hv₁w : v₁<2^w := by omega
    have hptrw : v₁-L<2^w := by omega
    refine runs_seq_call_le hmc (vs:=[a,v₁-L,L,P,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,_,_,rfl,hP,hwidth,by omega,by omega,valid_frozen fr₁ ha hva,
        hptr.symm ▸ hv₁,hprod⟩,hz₁,by change v₁+11*L+1<2^w; omega⟩
    · intro v mem₂ pos₂ hp₂
      rcases hp₂ with ⟨⟨he₂,hl₂,hh₂,fr₂,hz₂,hv₂,hval₂⟩,herr,houtB⟩
      change v=v₁+11*L+1 at he₂
      change (∀ z<v₁,mem₂ z=mem₁ z) at fr₂
      change Valid mem₂ (v₁+10*L+1) h L at hv₂
      change |fixVal mem₂ (v-L) h L P-fixVal mem₁ a h L P*fixVal mem₁ (v₁-L) h L P|≤1/(2:ℝ)^P at herr
      change |fixVal mem₂ (v-L) h L P|≤(2:ℝ)^(D+1) at houtB
      rw [hafix,hdiff] at herr
      have hptr₂ : v-L=v₁+10*L+1 := by omega
      have hvw : v<2^w := by omega
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change (heap≤v ∧ v≤heap+(13*L+1) ∧ (∀ z<heap,mem₂ z=mem z) ∧ ZeroFrom mem₂ v ∧ True) ∧
          Valid mem₂ (v-L) h L ∧
          |fixVal mem₂ (v-L) h L P-(fixVal mem a h L P*(fixVal mem u h L P-fixVal mem d h L P))|≤1/(2:ℝ)^P ∧
          |fixVal mem₂ (v-L) h L P|≤(2:ℝ)^(D+1)
        refine ⟨⟨by omega,by omega,?_,hz₂,trivial⟩,hptr₂.symm ▸ hv₂,herr,houtB⟩
        intro z hz
        rw [fr₂ z (by omega),fr₁ z hz]
      · simp only [weightedDifferenceContract,subtractContract,productContract,fixedMultiplyContract,heapContract,
          List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,
          argsSize_cons,argsSize_nil]
        ring_nf
        omega

end MinCostFlow.Num.IPM
