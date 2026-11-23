module

public import MinCostFlow.Num.PositiveExponential
public import MinCostFlow.Num.Reciprocal
public import MinCostFlow.Num.Absolute
public import MinCostFlow.Num.ExponentialReciprocalFacts
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Verified fixed-point exponential

Compute the exponential of the absolute argument. For a negative input, invert
that approximation using the verified reciprocal. Three additional relative
precision bits cover both computations. The contract states relative error
against the real exponential for every input of absolute value at most `B`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Space covers magnitude conversion, positive evaluation, and a reciprocal. -/
def exponentialSpace (L P B : ℕ) : ℕ :=
  L+positiveExponentialSpace L P B+fixedDivideSpace L

/-- Explicit polynomial cost, including the negative-input reciprocal. -/
def exponentialCost (L P B : ℕ) : ℕ :=
  positiveExponentialCost L P B+(3*L)*(900*L+644)+1000*L+1000

/-- Arguments `[y,one,L,P,B,heap]`. -/
def exponentialBody (negative absolute positive reciprocal : ℕ) : Stmt :=
  .call 6 negative [.reg 0,.reg 2] ;;
  .call 7 absolute [.reg 0,.reg 2,.reg 5] ;;
  .call 8 positive [.reg 5,.reg 1,.reg 2,.reg 3,.reg 4,.reg 7] ;;
  .cond (.reg 6)
    (.call 9 reciprocal [.reg 1,.bin .sub (.reg 8) (.reg 2),.reg 2,.reg 3,.reg 8] ;;
      .ret (.reg 9))
    (.ret (.reg 8))

/-- The signed exponential and its closed deterministic dependencies. -/
def exponentialModule (b h : ℕ) : List Stmt :=
  [exponentialBody (b+1) (b+2) (b+7) (b+65)] ++
    (isNegativeModule (b+1) h ++ (absoluteModule (b+2) h ++
      (positiveExponentialModule (b+7) h ++ reciprocalModule (b+65) h)))

/-- Exponential relative error on `|y|≤B`. The reusable one block has
numerator `2^P`. Precision `q+2B+20`, width `P+2B+4`, and the stated
word bounds cover both the positive exponential and the reciprocal.
The output is in the last `L` cells below the returned pointer. -/
def exponentialContract (w h q : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a one L P B heap,args=[a,one,L,P,B,heap] ∧ h∣P ∧
      q+2*B+20≤P ∧ P+2*B+4≤h*L ∧ 2*P+9<2^w ∧ a+L≤heap ∧ one+L≤heap ∧
      Valid mem a h L ∧ Valid mem one h L ∧ intVal mem one h L=(2:ℤ)^P ∧
      |fixVal mem a h L P|≤B)
    (fun _ _ _ => True)
    (fun args _ => exponentialCost (args.getD 2 0) (args.getD 3 0) (args.getD 4 0))
    (fun args _ => exponentialSpace (args.getD 2 0) (args.getD 3 0) (args.getD 4 0))
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧
      Valid mem' (v-args.getD 2 0) h (args.getD 2 0) ∧
      |fixVal mem' (v-args.getD 2 0) h (args.getD 2 0) (args.getD 3 0)-
        Real.exp (fixVal mem (args.getD 0 0) h (args.getD 2 0) (args.getD 3 0))|≤
        (1/(2:ℝ)^q)*Real.exp (fixVal mem (args.getD 0 0) h (args.getD 2 0) (args.getD 3 0)) }

/-- The exponential procedure is deterministic. -/
theorem exponentialModule_noRand (b h : ℕ) : ∀ s∈exponentialModule b h,s.NoRand := by
  intro s hs
  simp only [exponentialModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hn | ha | hp | hr
  · simp [exponentialBody,Stmt.NoRand]
  · have he : s=isNegativeBody h := by simpa [isNegativeModule] using hn
    subst s
    exact isNegativeBody_noRand _
  · exact absoluteModule_noRand _ _ _ ha
  · exact positiveExponentialModule_noRand _ _ _ hp
  · exact reciprocalModule_noRand _ _ _ hr

private theorem valid_frozen {mem mem' : ℕ→ℕ} {a h L heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) (hv : Valid mem a h L) :
    Valid mem' a h L := by
  intro i hi
  rw [hf _ (by omega)]
  exact hv i hi

private theorem value_frozen {mem mem' : ℕ→ℕ} {a h L heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) :
    intVal mem' a h L=intVal mem a h L := intVal_congr (fun i hi => hf _ (by omega))

/-- The exponential entry meets its real relative-error contract, including
all rounding in the negative-input reciprocal branch. -/
theorem exponential_meetsContract {w h b q : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (exponentialModule b h)) :
    MeetsContract w p b (exponentialContract w h q) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hn := hasAt_append_left ht
  have ht₂ := hasAt_append_right ht
  change p.HasAt (b+2) _ at ht₂
  have ha := hasAt_append_left ht₂
  have ht₃ := hasAt_append_right ht₂
  change p.HasAt (b+7) _ at ht₃
  have hpos := hasAt_append_left ht₃
  have hrecip := hasAt_append_right ht₃
  change p.HasAt (b+65) _ at hrecip
  have hb := base_lt_word (show 2*h+2≤w by omega)
  have hw1 : 1<2^w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  have hnC := isNegative_meetsContract hh hw1 hb hn
  have haC := absolute_meetsContract hh hw1 hb ha
  have hpC := positiveExponential_meetsContract (q:=q+3) hh hw hpos
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a,one,L,P,B,heap,rfl,hP,hprec,hwidth,hPw',ha,ho,hva,hvo,hone,hB⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+exponentialSpace L P B<2^w at hbound
  unfold exponentialSpace at hbound
  have hposSpace : L≤positiveExponentialSpace L P B := by unfold positiveExponentialSpace; omega
  have hFspace : L≤fixedDivideSpace L := by unfold fixedDivideSpace; omega
  have haw : a<2^w := hwords a (by simp)
  have how : one<2^w := hwords one (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPw : P<2^w := hwords P (by simp)
  have hBw : B<2^w := hwords B (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have hmagbound := exponential_magnitude_bound hB
  have hmagfit : Fits h L |intVal mem a h L| := fits_exp_range hwidth (abs_nonneg _) hmagbound
  have hε0 : (0:ℝ)≤1/(2:ℝ)^q := by positivity
  have hε1 : (1/(2:ℝ)^q)≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hguard : 1/(2:ℝ)^(q+3)=(1/(2:ℝ)^q)/8 := by rw [pow_add]; norm_num; ring
  apply runs_start_le
  unfold exponentialBody
  refine runs_seq_call_le hnC (vs:=[a,L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨_,_,rfl,by omega,hva⟩
  · intro flag mem₀ pos₀ hp₀
    rcases hp₀ with ⟨hmem,hflag⟩
    change mem₀=mem at hmem
    subst mem₀
    change flag=(if intVal mem a h L<0 then 1 else 0) at hflag
    refine runs_seq_call_le haC (vs:=[a,L,heap]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,rfl,ha,hva⟩,hz,by change heap+L<2^w; omega⟩
    · intro v₁ mem₁ pos₁ hp₁
      rcases hp₁ with ⟨hv₁,_,_,hf₁,hz₁,hvalid₁,hunsigned₁⟩
      change v₁=heap+L at hv₁
      change (∀ z<heap,mem₁ z=mem z) at hf₁
      change Valid mem₁ heap h L at hvalid₁
      change unsignedVal mem₁ heap h L=(intVal mem a h L).natAbs at hunsigned₁
      have hvalue₁ := magnitude_intVal hunsigned₁ hmagfit
      have hmag : fixVal mem₁ heap h L P=|fixVal mem a h L P| := by
        simp only [fixVal,hvalue₁,Int.cast_abs,abs_div,abs_of_pos (pow_pos (by norm_num : (0:ℝ)<2) P)]
      have hvo₁ := valid_frozen hf₁ ho hvo
      have hone₁ : intVal mem₁ one h L=(2:ℤ)^P := (value_frozen hf₁ ho).trans hone
      have hv₁w : v₁<2^w := by omega
      refine runs_seq_call_le hpC (vs:=[heap,one,L,P,B,v₁]) (by eval_expr) (by wram_words) ?_ ?_
      · refine ⟨⟨_,_,_,_,_,_,rfl,hP,by omega,hwidth,hPw',by omega,by omega,hvalid₁,hvo₁,hone₁,?_,?_⟩,
          hz₁,by change v₁+positiveExponentialSpace L P B<2^w; omega⟩
        · rw [hvalue₁]; exact abs_nonneg _
        · rw [hmag]; exact hB
      · intro v₂ mem₂ pos₂ hp₂
        rcases hp₂ with ⟨hv₂,_,_,hf₂,hz₂,hvalid₂,hlo₂,hhi₂,herr₂⟩
        change v₂=v₁+positiveExponentialSpace L P B at hv₂
        change (∀ z<v₁,mem₂ z=mem₁ z) at hf₂
        change Valid mem₂ (v₁+positiveExponentialSpace L P B-L) h L at hvalid₂
        change 1≤fixVal mem₂ (v₁+positiveExponentialSpace L P B-L) h L P at hlo₂
        change fixVal mem₂ (v₁+positiveExponentialSpace L P B-L) h L P≤Real.exp (fixVal mem₁ heap h L P) at hhi₂
        change |fixVal mem₂ (v₁+positiveExponentialSpace L P B-L) h L P-Real.exp (fixVal mem₁ heap h L P)|≤
          (1/(2:ℝ)^(q+3))*Real.exp (fixVal mem₁ heap h L P) at herr₂
        rw [← hv₂] at hvalid₂ hlo₂ hhi₂ herr₂
        rw [hmag] at hhi₂ herr₂
        have hvo₂ := valid_frozen hf₂ (by omega) hvo₁
        have hone₂ : intVal mem₂ one h L=(2:ℤ)^P := (value_frozen hf₂ (by omega)).trans hone₁
        have hv₂w : v₂<2^w := by omega
        have hptr₂w : v₂-L<2^w := by omega
        wram_step
        · have hflagpos : flag≠0 := by simpa [startState] using hcond
          have hneg : intVal mem a h L<0 := by
            by_contra he
            rw [ite_eq_right he] at hflag
            exact hflagpos hflag
          have hyneg : fixVal mem a h L P<0 := div_neg_of_neg_of_pos (by exact_mod_cast hneg) (by positivity)
          have htarget : Real.exp (fixVal mem a h L P)=1/Real.exp |fixVal mem a h L P| := by
            rw [abs_of_neg hyneg,Real.exp_neg,one_div,inv_inv]
          have hrC := reciprocal_meetsContract (E:=2*B) (q:=q+3) hh hw hrecip
          refine runs_seq_call_le hrC (vs:=[one,v₂-L,L,P,v₂]) (by eval_expr) (by wram_words) ?_ ?_
          · refine ⟨⟨_,_,_,_,_,rfl,hP,by omega,by omega,hvo₂,hvalid₂,hone₂,?_,?_,by omega,by omega⟩,
              hz₂,by change v₂+fixedDivideSpace L<2^w; omega⟩
            · have hh : (1/(2:ℝ)^(2*B))≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
              exact le_trans hh hlo₂
            · exact le_trans hhi₂ (exp_le_two_pow_twice hB)
          · intro v mem₃ pos₃ hp₃
            rcases hp₃ with ⟨⟨hv,_,_,hf₃,hz₃,hvalid₃,_⟩,herr₃⟩
            change v=v₂+fixedDivideSpace L at hv
            change (∀ z<v₂,mem₃ z=mem₂ z) at hf₃
            change Valid mem₃ (v₂+9*L+integerDivideSpace (3*L)) h L at hvalid₃
            change |fixVal mem₃ (v-L) h L P-1/fixVal mem₂ (v₂-L) h L P|≤
              (1/(2:ℝ)^(q+3))/fixVal mem₂ (v₂-L) h L P at herr₃
            have hout : v-L=v₂+9*L+integerDivideSpace (3*L) := by unfold fixedDivideSpace at hv; omega
            have herr := reciprocal_relative_compose
              (show 0<fixVal mem₂ (v₂-L) h L P by linarith only [hlo₂])
              (Real.exp_pos _) hhi₂ hε0 hε1 (by simpa only [hguard] using herr₂)
              (by simpa only [hguard] using herr₃)
            have hvw : v<2^w := by omega
            refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
            · change (heap≤v ∧ v≤heap+exponentialSpace L P B ∧ (∀ z<heap,mem₃ z=mem z) ∧
                ZeroFrom mem₃ v ∧ True) ∧ Valid mem₃ (v-L) h L ∧
                |fixVal mem₃ (v-L) h L P-Real.exp (fixVal mem a h L P)|≤
                  (1/(2:ℝ)^q)*Real.exp (fixVal mem a h L P)
              refine ⟨⟨by omega,?_,?_,hz₃,trivial⟩,?_,?_⟩
              · unfold exponentialSpace; omega
              · intro z hz
                exact (hf₃ z (by omega)).trans ((hf₂ z (by omega)).trans (hf₁ z hz))
              · rw [hout]; exact hvalid₃
              · rw [htarget]
                simpa only [div_eq_mul_inv,one_mul] using herr
            · simp only [exponentialContract,isNegativeContract,absoluteContract,positiveExponentialContract,
                reciprocalContract,fixedDivideContract,heapContract,List.getD_cons_zero,List.getD_cons_succ,
                Expr.size_reg,Expr.size_bin,Expr.size_const,argsSize_cons,argsSize_nil,exponentialCost]
              omega
        · have hflagzero : flag=0 := by simpa [startState] using hcond
          have hnneg : ¬intVal mem a h L<0 := by
            intro he
            rw [ite_eq_left he] at hflag
            omega
          have hynonneg : 0≤fixVal mem a h L P := div_nonneg (by exact_mod_cast (show 0≤ intVal mem a h L by omega)) (by positivity)
          have herr : |fixVal mem₂ (v₂-L) h L P-Real.exp (fixVal mem a h L P)|≤
              (1/(2:ℝ)^q)*Real.exp (fixVal mem a h L P) := by
            rw [abs_of_nonneg hynonneg] at herr₂
            have hq : 1/(2:ℝ)^(q+3)≤1/(2:ℝ)^q :=
              one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
            exact le_trans herr₂ (mul_le_mul_of_nonneg_right hq (le_of_lt (Real.exp_pos _)))
          refine runs_ret_le (v:=v₂) (by eval_expr) ?_ ?_
          · change (heap≤v₂ ∧ v₂≤heap+exponentialSpace L P B ∧ (∀ z<heap,mem₂ z=mem z) ∧
              ZeroFrom mem₂ v₂ ∧ True) ∧ Valid mem₂ (v₂-L) h L ∧
              |fixVal mem₂ (v₂-L) h L P-Real.exp (fixVal mem a h L P)|≤
                (1/(2:ℝ)^q)*Real.exp (fixVal mem a h L P)
            refine ⟨⟨by omega,?_,?_,hz₂,trivial⟩,hvalid₂,herr⟩
            · unfold exponentialSpace; omega
            · intro z hz
              exact (hf₂ z (by omega)).trans (hf₁ z hz)
          · simp only [exponentialContract,isNegativeContract,absoluteContract,positiveExponentialContract,
              heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,
              Expr.size_const,argsSize_cons,argsSize_nil,exponentialCost]
            omega

end MinCostFlow.Num
