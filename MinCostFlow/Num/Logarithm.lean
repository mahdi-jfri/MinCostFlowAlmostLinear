module

public import MinCostFlow.Num.RangeLogarithmCorrect
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Verified fixed-point natural logarithm

Construct a stored two from the reusable stored one, compute its logarithm,
and use that constant in range reduction. The normalized series calculation
and every range-reduction step are verified separately. Their error bounds
combine to an absolute error of `2⁻q` at precision at least `q+E+10`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Fresh cells used by the logarithm, including its constant calculation. -/
def logarithmSpace (L P E : ℕ) : ℕ :=
  L+normalizedLogarithmSpace L (P+4)+rangeLogarithmSpace L P E

/-- An explicit polynomial bound for the logarithm body. -/
def logarithmCost (L P E : ℕ) : ℕ :=
  (E+1)*(400*L+1000)+
    2*((P+4)*(500*L^2+2000*L+2000)+5000*L^2+10000*L+10000)+100*L+1000

/-- Arguments `[x,one,L,P,E,heap]`. -/
def logarithmBody (shift normalized range : ℕ) : Stmt :=
  .call 6 shift [.reg 1,.reg 2,.const 1,.reg 5] ;;
  .call 7 normalized [.reg 5,.reg 1,.reg 2,.reg 3,
    .bin .add (.reg 3) (.const 4),.reg 6] ;;
  .call 8 range [.reg 0,.reg 1,.reg 5,.bin .sub (.reg 7) (.reg 2),
    .reg 2,.reg 3,.reg 4,.reg 7] ;;
  .ret (.reg 8)

/-- The logarithm entry and all deterministic dependencies. -/
def logarithmModule (b h : ℕ) : List Stmt :=
  [logarithmBody (b+1) (b+3) (b+94)] ++
    (shiftLeftModule (b+1) h ++ (normalizedLogarithmModule (b+3) h ++
      rangeLogarithmModule (b+94) h))

/-- Absolute logarithm error on `[2⁻ᴱ,2ᴱ]`. The reusable constant `one`
has integer numerator `2^P`. The conditions `q+E+10≤P`, `P+E+4≤h*L`,
and `2*P+9<2^w` cover precision, intermediate range, and series denominators.
The output occupies the last `L` cells below the returned heap pointer. -/
def logarithmContract (w h q : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a one L P E heap,args=[a,one,L,P,E,heap] ∧ h∣P ∧
      q+E+10≤P ∧ P+E+4≤h*L ∧ 2*P+9<2^w ∧ a+L≤heap ∧ one+L≤heap ∧
      Valid mem a h L ∧ Valid mem one h L ∧ intVal mem one h L=(2:ℤ)^P ∧
      1/(2:ℝ)^E≤fixVal mem a h L P ∧ fixVal mem a h L P≤(2:ℝ)^E)
    (fun _ _ _ => True)
    (fun args _ => logarithmCost (args.getD 2 0) (args.getD 3 0) (args.getD 4 0))
    (fun args _ => logarithmSpace (args.getD 2 0) (args.getD 3 0) (args.getD 4 0))
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧
      Valid mem' (v-args.getD 2 0) h (args.getD 2 0) ∧
      |fixVal mem' (v-args.getD 2 0) h (args.getD 2 0) (args.getD 3 0)-
        Real.log (fixVal mem (args.getD 0 0) h (args.getD 2 0) (args.getD 3 0))|≤1/(2:ℝ)^q }

/-- The logarithm module contains no random statement. -/
theorem logarithmModule_noRand (b h : ℕ) : ∀ s∈logarithmModule b h,s.NoRand := by
  intro s hs
  simp only [logarithmModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hshift | hn | hr
  · simp [logarithmBody,Stmt.NoRand]
  · exact shiftLeftModule_noRand _ _ _ hshift
  · exact normalizedLogarithmModule_noRand _ _ _ hn
  · exact rangeLogarithmModule_noRand _ _ _ hr

private theorem valid_frozen {mem mem' : ℕ→ℕ} {a h L heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) (hv : Valid mem a h L) :
    Valid mem' a h L := by
  intro i hi
  rw [hf _ (by omega)]
  exact hv i hi

private theorem value_frozen {mem mem' : ℕ→ℕ} {a h L heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) :
    intVal mem' a h L=intVal mem a h L := intVal_congr (fun i hi => hf _ (by omega))

/-- The logarithm entry computes its constant internally and meets the real
absolute-error contract for every random tape. -/
theorem logarithm_meetsContract {w h b q : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (logarithmModule b h)) :
    MeetsContract w p b (logarithmContract w h q) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hs := hasAt_append_left ht
  have ht₂ := hasAt_append_right ht
  change p.HasAt (b+3) _ at ht₂
  have hn := hasAt_append_left ht₂
  have hr := hasAt_append_right ht₂
  change p.HasAt (b+94) _ at hr
  have hsC := shiftLeft_meetsContract hh (show 2*h+2≤w by omega) hs
  have hnC := normalizedLogarithm_meetsContract hh hw hn
  have hrC := rangeLogarithm_meetsContract hh hw hr
  have hw1 : 1<2^w := by
    have hb := base_lt_word (show 2*h+2≤w by omega)
    exact lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a,one,L,P,E,heap,rfl,hP,hprec,hwidth,hPw',ha,ho,hva,hvo,hone,hlo,hhi⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+logarithmSpace L P E<2^w at hbound
  unfold logarithmSpace at hbound
  have hP10 : 10≤P := by omega
  have hnormSpace : L≤normalizedLogarithmSpace L (P+4) := by unfold normalizedLogarithmSpace; omega
  have hspace : L≤rangeLogarithmSpace L P E := by unfold rangeLogarithmSpace; omega
  have hscale : (0:ℤ)<(2:ℤ)^P := by positivity
  have htwofit : Fits h L ((2:ℤ)^P*2) := fits_four_scale (P:=P) (by omega) (by omega) (by omega)
  have hpR : (0:ℝ)<(2:ℝ)^P := by positivity
  have heR : (0:ℝ)<(2:ℝ)^E := by positivity
  have hNlo : (2:ℤ)^P≤(2:ℤ)^E*intVal mem a h L := by
    have hh := (le_div_iff₀ hpR).mp hlo
    have hh0 : (2:ℝ)^P/(2:ℝ)^E≤(intVal mem a h L:ℝ) := by
      convert hh using 1 <;> ring
    have hh' := (div_le_iff₀ heR).mp hh0
    have hh'' : (2:ℝ)^P≤(2:ℝ)^E*(intVal mem a h L:ℝ) := by
      nlinarith only [hh']
    exact_mod_cast hh''
  have hNhi : intVal mem a h L≤(2:ℤ)^(E+1)*(2:ℤ)^P := by
    have hh := (div_le_iff₀ hpR).mp hhi
    have he : (2:ℝ)^E≤(2:ℝ)^(E+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hh' := le_trans hh (mul_le_mul_of_nonneg_right he (le_of_lt hpR))
    exact_mod_cast hh'
  have haw : a<2^w := hwords a (by simp)
  have how : one<2^w := hwords one (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPw : P<2^w := hwords P (by simp)
  have hEw : E<2^w := hwords E (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have hP4w : P+4<2^w := by omega
  apply runs_start_le
  unfold logarithmBody
  refine runs_seq_call_le hsC (vs:=[one,L,1,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,rfl,ho,hvo⟩,hz,by change heap+L<2^w; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨hv₁,_,_,hf₁,hz₁,hvalid₁,hvalue₁⟩
    change v₁=heap+L at hv₁
    change (∀ z<heap,mem₁ z=mem z) at hf₁
    change Valid mem₁ heap h L at hvalid₁
    change intVal mem₁ heap h L=wrap h L (intVal mem one h L*(2:ℤ)^1) at hvalue₁
    rw [hone,pow_one,wrap_of_fits htwofit] at hvalue₁
    have hone₁ : intVal mem₁ one h L=(2:ℤ)^P := (value_frozen hf₁ ho).trans hone
    have hvo₁ := valid_frozen hf₁ ho hvo
    have hv₁w : v₁<2^w := by omega
    refine runs_seq_call_le hnC (vs:=[heap,one,L,P,P+4,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · refine ⟨⟨_,_,_,_,_,_,rfl,hP,by omega,by omega,by omega,hvalid₁,hvo₁,hone₁,?_,?_,
        log_series_denominator_bound hP10,by omega⟩,hz₁,
        by change v₁+normalizedLogarithmSpace L (P+4)<2^w; omega⟩
      · rw [hvalue₁]; omega
      · rw [hvalue₁]; omega
    · intro v₂ mem₂ pos₂ hp₂
      rcases hp₂ with ⟨hv₂,_,_,hf₂,hz₂,hvalid₂,hvalue₂⟩
      change v₂=v₁+normalizedLogarithmSpace L (P+4) at hv₂
      change (∀ z<v₁,mem₂ z=mem₁ z) at hf₂
      change Valid mem₂ (v₁+normalizedLogarithmSpace L (P+4)-L) h L at hvalid₂
      change intVal mem₂ (v₁+normalizedLogarithmSpace L (P+4)-L) h L=
        normalizedLogInt P (intVal mem₁ heap h L) (P+4) at hvalue₂
      rw [← hv₂,hvalue₁] at hvalue₂
      rw [← hv₂] at hvalid₂
      have heTwo : (2:ℤ)^P*2=2*(2:ℤ)^P := mul_comm _ _
      rw [heTwo] at hvalue₂
      obtain ⟨_,_,hC0,hC1⟩ := normalizedLogInt_bounds
        (show (2:ℤ)^P≤2*(2:ℤ)^P by omega) (le_refl (2*(2:ℤ)^P)) (P+4)
      have hCerror : |(intVal mem₂ (v₂-L) h L:ℝ)/(2:ℝ)^P-Real.log 2|≤17/(2:ℝ)^P := by
        rw [hvalue₂]
        have hh := normalizedLogInt_error
          (show (2:ℤ)^P≤2*(2:ℤ)^P by omega) (le_refl (2*(2:ℤ)^P))
        have he : ((2*(2:ℤ)^P:ℤ):ℝ)/(2:ℝ)^P=2 := by push_cast; field_simp
        rw [he] at hh
        exact hh
      have hva₂ := valid_frozen hf₂ (by omega) (valid_frozen hf₁ ha hva)
      have hvo₂ := valid_frozen hf₂ (by omega) hvo₁
      have hvt₂ := valid_frozen hf₂ (by omega) hvalid₁
      have ha₂ : intVal mem₂ a h L=intVal mem a h L :=
        (value_frozen hf₂ (by omega)).trans (value_frozen hf₁ ha)
      have ho₂ : intVal mem₂ one h L=(2:ℤ)^P := (value_frozen hf₂ (by omega)).trans hone₁
      have ht₂ : intVal mem₂ heap h L=2*(2:ℤ)^P := by
        rw [value_frozen hf₂ (by omega),hvalue₁,heTwo]
      have hv₂w : v₂<2^w := by omega
      have hptr₂w : v₂-L<2^w := by omega
      refine runs_seq_call_le hrC (vs:=[a,one,heap,v₂-L,L,P,E,v₂]) (by eval_expr) (by wram_words) ?_ ?_
      · refine ⟨⟨_,_,_,_,_,_,_,_,rfl,hP,hP10,hwidth,hPw',by omega,by omega,by omega,by omega,
          hva₂,hvo₂,hvt₂,hvalid₂,ho₂,ht₂,?_,?_,?_,?_⟩,
          hz₂,by change v₂+rangeLogarithmSpace L P E<2^w; omega⟩
        · rw [hvalue₂]; exact hC0
        · rw [hvalue₂]; exact hC1
        · rw [ha₂]; exact hNlo
        · rw [ha₂]; exact hNhi
      · intro v mem₃ pos₃ hp₃
        rcases hp₃ with ⟨⟨hlo₃,hhi₃,hf₃,hz₃,_⟩,hvalid₃,hvalue₃⟩
        change v₂≤v at hlo₃
        change v≤v₂+rangeLogarithmSpace L P E at hhi₃
        change (∀ z<v₂,mem₃ z=mem₂ z) at hf₃
        change Valid mem₃ (v-L) h L at hvalid₃
        change intVal mem₃ (v-L) h L=rangeLogInt P (intVal mem₂ (v₂-L) h L) E
          (intVal mem₂ a h L) at hvalue₃
        rw [ha₂] at hvalue₃
        have hvw : v<2^w := by omega
        refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
        · change (heap≤v ∧ v≤heap+logarithmSpace L P E ∧ (∀ z<heap,mem₃ z=mem z) ∧
            ZeroFrom mem₃ v ∧ True) ∧ Valid mem₃ (v-L) h L ∧
            |fixVal mem₃ (v-L) h L P-Real.log (fixVal mem a h L P)|≤1/(2:ℝ)^q
          refine ⟨⟨by omega,?_,?_,hz₃,trivial⟩,hvalid₃,?_⟩
          · unfold logarithmSpace; omega
          · intro z hz
            exact (hf₃ z (by omega)).trans ((hf₂ z (by omega)).trans (hf₁ z hz))
          · change |(intVal mem₃ (v-L) h L:ℝ)/(2:ℝ)^P-
              Real.log ((intVal mem a h L:ℝ)/(2:ℝ)^P)|≤_
            rw [hvalue₃]
            exact le_trans (rangeLogInt_error hCerror E _ hNlo hNhi) (log_range_error_budget hprec)
        · simp only [logarithmContract,shiftLeftContract,normalizedLogarithmContract,rangeLogarithmContract,
            heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,
            Expr.size_const,argsSize_cons,argsSize_nil,logarithmCost,rangeLogarithmCost]
          ring_nf
          omega

end MinCostFlow.Num
