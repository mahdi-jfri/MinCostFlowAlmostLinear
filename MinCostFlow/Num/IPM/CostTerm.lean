module

public import MinCostFlow.Num.IPM.IntegerTimes
public import MinCostFlow.Num.IPM.DivideFacts
public import MinCostFlow.Num.LoadSmall
public import MinCostFlow.Num.ShiftLeft
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Computing the gradient's cost term

For Definition 4.2 of Chen et al. (page 24), first load `20m`, multiply
by the integer edge cost, and shift to precision `P`. These steps are
exact. Division by the residual then introduces at most one output unit
of error, regardless of the size of the integer coefficient.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[m,cost,residual,L,P,heap]`. -/
def costTermBody (load mul shift divide : ℕ) : Stmt :=
  .call 6 load [.bin .mul (.const 20) (.reg 0),.reg 3,.reg 5] ;;
  .call 7 mul [.reg 5,.reg 1,.reg 3,.reg 6] ;;
  .call 8 shift [.bin .sub (.reg 7) (.reg 3),.reg 3,.reg 4,.reg 7] ;;
  .call 9 divide [.reg 7,.reg 2,.reg 3,.reg 4,.reg 8] ;;
  .ret (.reg 9)

/-- The cost-term entry and its closed arithmetic dependencies. -/
def costTermModule (b h : ℕ) : List Stmt :=
  [costTermBody (b+1) (b+2) (b+9) (b+11)] ++
    (loadSmallModule (b+1) h ++ (integerTimesModule (b+2) h ++
      (shiftLeftModule (b+9) h ++ fixedDivideModule (b+11) h)))

/-- Space for the coefficient, its product, its scaling, and division. -/
def costTermSpace (L : ℕ) := 9*L+fixedDivideSpace L

/-- Explicit quadratic arithmetic cost. -/
def costTermCost (L : ℕ) :=
  152*L^2+265*L+500+((3*L)*(900*L+644)+900*L+700)

/-- The size parameter `K` bounds both `20m` and `|20mc|`.
Together with the residual range, width `P+K+E+3` prevents all overflow.
The final block starts at `v-L`, with absolute error at most `2^-P`. -/
def costTermContract (w h E K : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ m c r L P heap,args=[m,c,r,L,P,heap] ∧ h∣P ∧
      P+K+E+3≤h*L ∧ 20*m<2^w ∧ 20*m≤2^K ∧
      |20*(m:ℤ)*intVal mem c h L|≤(2:ℤ)^K ∧
      c+L≤heap ∧ r+L≤heap ∧ Valid mem c h L ∧ Valid mem r h L ∧
      1/(2:ℝ)^E≤fixVal mem r h L P ∧ fixVal mem r h L P≤(2:ℝ)^E)
    (fun _ _ _ => True)
    (fun args _ => costTermCost (args.getD 3 0))
    (fun args _ => costTermSpace (args.getD 3 0))
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧
      Valid mem' (v-args.getD 3 0) h (args.getD 3 0) ∧
      |fixVal mem' (v-args.getD 3 0) h (args.getD 3 0) (args.getD 4 0)-
        (20*(args.getD 0 0:ℝ)*(fixVal mem (args.getD 2 0) h (args.getD 3 0) (args.getD 4 0))⁻¹*
          (intVal mem (args.getD 1 0) h (args.getD 3 0):ℝ))|≤1/(2:ℝ)^(args.getD 4 0)}

/-- No part of cost-term computation uses random bits. -/
theorem costTermModule_noRand (b h : ℕ) : ∀ s∈costTermModule b h,s.NoRand := by
  intro s hs
  simp only [costTermModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hl | hm | hs | hd
  · simp [costTermBody,Stmt.NoRand]
  · simp only [loadSmallModule,List.mem_singleton] at hl
    subst s
    exact loadSmallBody_noRand _ _
  · exact integerTimesModule_noRand _ _ _ hm
  · exact shiftLeftModule_noRand _ _ _ hs
  · exact fixedDivideModule_noRand _ _ _ hd

private theorem loaded_fits {h L n heap : ℕ} {mem : ℕ→ℕ}
    (hl : ListAt mem heap (digits h L n)) (hf : Fits h L (n:ℤ)) :
    intVal mem heap h L=(n:ℤ) := by
  rw [(loadSmall_value hl).2.2]
  have he : residue h L (n:ℤ)=n%capacity h L := by
    simp only [residue,← Int.natCast_mod,Int.toNat_natCast]
  rw [← he]
  exact wrap_of_fits hf

set_option maxRecDepth 8192 in
/-- The integer coefficient and its scaling are exact, leaving only the
single floor at the output of fixed-point division. -/
theorem costTerm_meetsContract {w h b E K : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (costTermModule b h)) :
    MeetsContract w p b (costTermContract w h E K) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hl := hasAt_append_left ht
  have ht₂ := hasAt_append_right ht
  change p.HasAt (b+2) _ at ht₂
  have hm := hasAt_append_left ht₂
  have ht₃ := hasAt_append_right ht₂
  change p.HasAt (b+9) _ at ht₃
  have hs := hasAt_append_left ht₃
  have hd := hasAt_append_right ht₃
  change p.HasAt (b+11) _ at hd
  have hw' : 2*h+2≤w := by omega
  have hw1 : 1<2^w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) (base_lt_word hw')
  have hw20 : 20<2^w := lt_of_lt_of_le (by decide : 20<2^5)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hlc := loadSmall_meetsContract hw1 (base_lt_word hw') hl
  have hmc := integerTimes_meetsContract hh hw' hm
  have hsc := shiftLeft_meetsContract hh hw' hs
  have hdc := fixedDivide_meetsContract hh hw hd
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨m,c,r,L,P,heap,rfl,hP,hwidth,hmword,hmBound,hcBound,hc,hr,hvc,hvr,hrl,hrh⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+costTermSpace L<2^w at hbound
  have hdivSpace : L≤fixedDivideSpace L := by unfold fixedDivideSpace; omega
  have hmword' : m<2^w := hwords m (by simp)
  have hcword : c<2^w := hwords c (by simp)
  have hrword : r<2^w := hwords r (by simp)
  have hLword : L<2^w := hwords L (by simp)
  have hPword : P<2^w := hwords P (by simp)
  have hheapword : heap<2^w := hwords heap (by simp)
  have hmReal : |((20*m:ℕ):ℝ)|≤(2:ℝ)^K := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hmBound
  have hcReal : |20*(m:ℝ)*(intVal mem c h L:ℝ)|≤(2:ℝ)^K := by exact_mod_cast hcBound
  have hmFit : Fits h L ((20*m:ℕ):ℤ) :=
    fits_of_scaled_bound (P:=0) (E:=K) (by omega) (by simpa only [pow_zero,div_one,Int.cast_natCast] using hmReal)
  have hcFit : Fits h L (20*(m:ℤ)*intVal mem c h L) :=
    fits_of_scaled_bound (P:=0) (E:=K) (by omega) (by simpa only [pow_zero,div_one,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] using hcReal)
  have hsFit : Fits h L ((20*(m:ℤ)*intVal mem c h L)*(2:ℤ)^P) := by
    apply fits_of_scaled_bound (P:=P) (E:=K) (by omega)
    simpa only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_natCast,mul_div_cancel_right₀ _ (by positivity : (2:ℝ)^P≠0)] using hcReal
  apply runs_start_le
  unfold costTermBody
  refine runs_seq_call_le hlc (vs:=[20*m,L,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,rfl⟩,hz,by change heap+L<2^w; unfold costTermSpace at hbound; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨he₁,hl₁,hh₁,fr₁,hz₁,hlist₁⟩
    change v₁=heap+L at he₁
    change (∀ z<heap,mem₁ z=mem z) at fr₁
    change ListAt mem₁ heap (digits h L (20*m)) at hlist₁
    have hv₁ := (loadSmall_value hlist₁).1
    have hval₁ := loaded_fits hlist₁ hmFit
    have hcv₁ := value_frozen (h:=h) fr₁ hc
    have hprodFit : Fits h L (intVal mem₁ heap h L*intVal mem₁ c h L) := by
      rw [hval₁,hcv₁]
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using hcFit
    have hv₁word : v₁<2^w := by unfold costTermSpace at hbound; omega
    refine runs_seq_call_le hmc (vs:=[heap,c,L,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,_,rfl,by omega,by omega,hv₁,valid_frozen fr₁ hc hvc,hprodFit⟩,hz₁,
        by change v₁+7*L<2^w; unfold costTermSpace at hbound; omega⟩
    · intro v₂ mem₂ pos₂ hp₂
      rcases hp₂ with ⟨he₂,hl₂,hh₂,fr₂,hz₂,hv₂,hval₂⟩
      change v₂=v₁+7*L at he₂
      change (∀ z<v₁,mem₂ z=mem₁ z) at fr₂
      change Valid mem₂ (v₁+6*L) h L at hv₂
      change intVal mem₂ (v₁+6*L) h L=intVal mem₁ heap h L*intVal mem₁ c h L at hval₂
      rw [hval₁,hcv₁] at hval₂
      simp only [Nat.cast_mul,Nat.cast_ofNat] at hval₂
      have hptr₂ : v₂-L=v₁+6*L := by omega
      have hrfix₂ : fixVal mem₂ r h L P=fixVal mem r h L P :=
        (fixVal_frozen fr₂ (by omega)).trans (fixVal_frozen fr₁ hr)
      have hrv₂ : Valid mem₂ r h L := valid_frozen fr₂ (by omega) (valid_frozen fr₁ hr hvr)
      have hv₂word : v₂<2^w := by unfold costTermSpace at hbound; omega
      have hptr₂word : v₂-L<2^w := by omega
      refine runs_seq_call_le hsc (vs:=[v₂-L,L,P,v₂]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨_,_,_,_,rfl,by omega,hptr₂.symm ▸ hv₂⟩,hz₂,
          by change v₂+L<2^w; unfold costTermSpace at hbound; omega⟩
      · intro v₃ mem₃ pos₃ hp₃
        rcases hp₃ with ⟨he₃,hl₃,hh₃,fr₃,hz₃,hv₃,hval₃⟩
        change v₃=v₂+L at he₃
        change (∀ z<v₂,mem₃ z=mem₂ z) at fr₃
        change Valid mem₃ v₂ h L at hv₃
        change intVal mem₃ v₂ h L=wrap h L (intVal mem₂ (v₂-L) h L*(2:ℤ)^P) at hval₃
        rw [hptr₂,hval₂,wrap_of_fits hsFit] at hval₃
        have hcoefFix : fixVal mem₃ v₂ h L P=20*(m:ℝ)*(intVal mem c h L:ℝ) := by
          simp only [fixVal,hval₃,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_natCast]
          exact mul_div_cancel_right₀ _ (by positivity)
        have hrfix₃ : fixVal mem₃ r h L P=fixVal mem r h L P :=
          (fixVal_frozen fr₃ (by omega)).trans hrfix₂
        have hrvalid₃ := valid_frozen fr₃ (show r+L≤v₂ by omega) hrv₂
        have hrpos : 0<fixVal mem₃ r h L P := by rw [hrfix₃]; exact lt_of_lt_of_le (by positivity) hrl
        have hrne : intVal mem₃ r h L≠0 := by
          intro he
          have he' : fixVal mem₃ r h L P=0 := by simp only [fixVal,he,Int.cast_zero,zero_div]
          linarith only [hrpos,he']
        have hquotFit : Fits h L (floorDiv (intVal mem₃ v₂ h L*(2:ℤ)^P) (intVal mem₃ r h L)) := by
          rw [fixed_divide_floor]
          apply floor_scaled_fits (D:=K+E) _ (by omega)
          rw [hcoefFix,hrfix₃]
          exact quotient_bound hcReal hrl
        have hv₃word : v₃<2^w := by unfold costTermSpace at hbound; omega
        refine runs_seq_call_le hdc (vs:=[v₂,r,L,P,v₃]) (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨⟨_,_,_,_,_,rfl,hP,by omega,by omega,hv₃,hrvalid₃,hrne,hquotFit⟩,hz₃,
            by change v₃+fixedDivideSpace L<2^w; unfold costTermSpace at hbound; omega⟩
        · intro v mem₄ pos₄ hp₄
          have herr := fixedDivide_output_error hp₄
          rcases hp₄ with ⟨he₄,hl₄,hh₄,fr₄,hz₄,hv₄,hval₄⟩
          change v=v₃+fixedDivideSpace L at he₄
          change (∀ z<v₃,mem₄ z=mem₃ z) at fr₄
          change Valid mem₄ (v₃+9*L+integerDivideSpace (3*L)) h L at hv₄
          rw [hcoefFix,hrfix₃] at herr
          have htarget : (20*(m:ℝ)*(intVal mem c h L:ℝ))/fixVal mem r h L P=
              20*(m:ℝ)*(fixVal mem r h L P)⁻¹*(intVal mem c h L:ℝ) := by rw [div_eq_mul_inv]; ring
          rw [htarget] at herr
          have hvword : v<2^w := by unfold costTermSpace at hbound; omega
          have hptr₄ : v-L=v₃+9*L+integerDivideSpace (3*L) := by rw [he₄]; unfold fixedDivideSpace; omega
          refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
          · change (heap≤v ∧ v≤heap+costTermSpace L ∧ (∀ z<heap,mem₄ z=mem z) ∧ ZeroFrom mem₄ v ∧ True) ∧
              Valid mem₄ (v-L) h L ∧
              |fixVal mem₄ (v-L) h L P-(20*(m:ℝ)*(fixVal mem r h L P)⁻¹*(intVal mem c h L:ℝ))|≤1/(2:ℝ)^P
            refine ⟨⟨by omega,?_,?_,hz₄,trivial⟩,hptr₄.symm ▸ hv₄,herr⟩
            · unfold costTermSpace; omega
            · intro z hz
              rw [fr₄ z (by omega),fr₃ z (by omega),fr₂ z (by omega),fr₁ z hz]
          · simp only [costTermContract,loadSmallContract,integerTimesContract,shiftLeftContract,fixedDivideContract,heapContract,
              List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,
              argsSize_cons,argsSize_nil,costTermCost]
            omega

/-- A coefficient bound and residual lower bound also bound the stored cost
term, including its one output rounding. -/
theorem costTerm_output_range {w h E K m c r L P heap v : ℕ} {mem mem' : ℕ→ℕ}
    (hout : (costTermContract w h E K).post [m,c,r,L,P,heap] mem v mem')
    (hc : |20*(m:ℝ)*(intVal mem c h L:ℝ)|≤(2:ℝ)^K)
    (hr : 1/(2:ℝ)^E≤fixVal mem r h L P) :
    |fixVal mem' (v-L) h L P|≤(2:ℝ)^(K+E+1) := by
  have he := hout.2.2
  change |fixVal mem' (v-L) h L P-
    (20*(m:ℝ)*(fixVal mem r h L P)⁻¹*(intVal mem c h L:ℝ))|≤1/(2:ℝ)^P at he
  have hq := quotient_bound hc hr
  have ht : (20*(m:ℝ)*(intVal mem c h L:ℝ))/fixVal mem r h L P=
      20*(m:ℝ)*(fixVal mem r h L P)⁻¹*(intVal mem c h L:ℝ) := by rw [div_eq_mul_inv]; ring
  rw [ht] at hq
  have hab : |fixVal mem' (v-L) h L P|≤
      |fixVal mem' (v-L) h L P-(20*(m:ℝ)*(fixVal mem r h L P)⁻¹*(intVal mem c h L:ℝ))|+
      |20*(m:ℝ)*(fixVal mem r h L P)⁻¹*(intVal mem c h L:ℝ)| := by
    simpa only [sub_add_cancel] using abs_add_le
      (fixVal mem' (v-L) h L P-(20*(m:ℝ)*(fixVal mem r h L P)⁻¹*(intVal mem c h L:ℝ)))
      (20*(m:ℝ)*(fixVal mem r h L P)⁻¹*(intVal mem c h L:ℝ))
  have hu : 1/(2:ℝ)^P≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hp : (1:ℝ)≤(2:ℝ)^(K+E) := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  linarith only [hab,he,hq,hu,hp]

end MinCostFlow.Num.IPM
