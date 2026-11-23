module

public import MinCostFlow.Num.Logarithm
public import MinCostFlow.Num.Exponential
public import MinCostFlow.Num.NegativePowerRoundingFacts
public import MinCostFlow.Num.Negate
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Verified negative real powers

Compute the logarithm, multiply by the stored exponent, negate the rounded
product, and evaluate the exponential. Guard precision covers each error in
that order. The final contract concerns the original fixed-point base and
exponent and the real power function.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Space for logarithm, product, negation, and exponential workspaces. -/
def negativePowerSpace (L P E : ℕ) : ℕ :=
  logarithmSpace L P E+(11*L+1)+L+exponentialSpace L P (2*E+4)

/-- Explicit polynomial cost of negative power evaluation. -/
def negativePowerCost (L P E : ℕ) : ℕ :=
  logarithmCost L P E+exponentialCost L P (2*E+4)+200*L^2+500*L+1000

/-- Arguments `[x,exponent,one,L,P,E,heap]`. -/
def negativePowerBody (log mul neg exp : ℕ) : Stmt :=
  .call 7 log [.reg 0,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6] ;;
  .call 8 mul [.reg 1,.bin .sub (.reg 7) (.reg 3),.reg 3,.reg 4,.reg 7] ;;
  .call 9 neg [.bin .sub (.reg 8) (.reg 3),.reg 3,.reg 8] ;;
  .call 10 exp [.bin .sub (.reg 9) (.reg 3),.reg 2,.reg 3,.reg 4,
    .bin .add (.bin .mul (.const 2) (.reg 5)) (.const 4),.reg 9] ;;
  .ret (.reg 10)

/-- Negative power evaluation and its closed arithmetic dependencies. -/
def negativePowerModule (b h : ℕ) : List Stmt :=
  [negativePowerBody (b+1) (b+202) (b+213) (b+215)] ++
    (logarithmModule (b+1) h ++ (fixedMultiplyModule (b+202) h ++
      (negateModule (b+213) h ++ exponentialModule (b+215) h)))

/-- Relative error for `x^(-a)` with `2⁻ᴱ≤x≤2ᴱ` and `0≤a≤2`.
The exponent and base are read at the shared precision. Precision
`q+4E+40` and width `P+4E+20` cover small outputs near `2⁻²ᴱ`.
The reusable one block has numerator `2^P`. Output is at `v-L`.
-/
def negativePowerContract (w h q : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a d one L P E heap,args=[a,d,one,L,P,E,heap] ∧ h∣P ∧
      q+4*E+40≤P ∧ P+4*E+20≤h*L ∧ 2*P+9<2^w ∧
      a+L≤heap ∧ d+L≤heap ∧ one+L≤heap ∧
      Valid mem a h L ∧ Valid mem d h L ∧ Valid mem one h L ∧
      intVal mem one h L=(2:ℤ)^P ∧ 1/(2:ℝ)^E≤fixVal mem a h L P ∧
      fixVal mem a h L P≤(2:ℝ)^E ∧ 0≤fixVal mem d h L P ∧ fixVal mem d h L P≤2)
    (fun _ _ _ => True)
    (fun args _ => negativePowerCost (args.getD 3 0) (args.getD 4 0) (args.getD 5 0))
    (fun args _ => negativePowerSpace (args.getD 3 0) (args.getD 4 0) (args.getD 5 0))
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧
      Valid mem' (v-args.getD 3 0) h (args.getD 3 0) ∧
      |fixVal mem' (v-args.getD 3 0) h (args.getD 3 0) (args.getD 4 0)-
        (Real.rpow (fixVal mem (args.getD 0 0) h (args.getD 3 0) (args.getD 4 0))
          (-fixVal mem (args.getD 1 0) h (args.getD 3 0) (args.getD 4 0)))|≤
        (1/(2:ℝ)^q)*(Real.rpow (fixVal mem (args.getD 0 0) h (args.getD 3 0) (args.getD 4 0))
          (-fixVal mem (args.getD 1 0) h (args.getD 3 0) (args.getD 4 0))) }

/-- Every body in the negative-power module is deterministic. -/
theorem negativePowerModule_noRand (b h : ℕ) : ∀ s∈negativePowerModule b h,s.NoRand := by
  intro s hs
  simp only [negativePowerModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hl | hm | hn | he
  · simp [negativePowerBody,Stmt.NoRand]
  · exact logarithmModule_noRand _ _ _ hl
  · exact fixedMultiplyModule_noRand _ _ _ hm
  · exact negateModule_noRand _ _ _ hn
  · exact exponentialModule_noRand _ _ _ he

private theorem valid_frozen {mem mem' : ℕ→ℕ} {a h L heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) (hv : Valid mem a h L) :
    Valid mem' a h L := by
  intro i hi
  rw [hf _ (by omega)]
  exact hv i hi

private theorem value_frozen {mem mem' : ℕ→ℕ} {a h L heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) :
    intVal mem' a h L=intVal mem a h L := intVal_congr (fun i hi => hf _ (by omega))

set_option maxRecDepth 4096 in
/-- Negative power evaluation meets its relative real-power contract for every
random tape. The product and its negation fit by the logarithm range bound. -/
theorem negativePower_meetsContract {w h b q : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (negativePowerModule b h)) :
    MeetsContract w p b (negativePowerContract w h q) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hl := hasAt_append_left ht
  have ht₂ := hasAt_append_right ht
  change p.HasAt (b+202) _ at ht₂
  have hm := hasAt_append_left ht₂
  have ht₃ := hasAt_append_right ht₂
  change p.HasAt (b+213) _ at ht₃
  have hn := hasAt_append_left ht₃
  have he := hasAt_append_right ht₃
  change p.HasAt (b+215) _ at he
  have hb := base_lt_word (show 2*h+2≤w by omega)
  have hw1 : 1<2^w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  have hlC := logarithm_meetsContract (q:=q+5) hh hw hl
  have hmC := fixedMultiply_meetsContract hh (show 2*h+2≤w by omega) hm
  have hnC := negate_meetsContract hw1 hb hn
  have heC := exponential_meetsContract (q:=q+2) hh hw he
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a,d,one,L,P,E,heap,rfl,hP,hprec,hwidth,hPw',ha,hd,ho,hva,hvd,hvo,hone,hlo,hhi,hd0,hd2⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+negativePowerSpace L P E<2^w at hbound
  unfold negativePowerSpace at hbound
  have hlogSpace : L≤logarithmSpace L P E := by unfold logarithmSpace; omega
  have hexpSpace : L≤exponentialSpace L P (2*E+4) := by unfold exponentialSpace; omega
  have haw : a<2^w := hwords a (by simp)
  have hdw : d<2^w := hwords d (by simp)
  have how : one<2^w := hwords one (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPw : P<2^w := hwords P (by simp)
  have hEw : E<2^w := hwords E (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have h2Ew : 2*E<2^w := by omega
  have hBw : 2*E+4<2^w := by omega
  have hxpos : 0<fixVal mem a h L P := lt_of_lt_of_le (by positivity) hlo
  have hε0 : (0:ℝ)≤1/(2:ℝ)^q := by positivity
  have hε1 : 1/(2:ℝ)^q≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hq5 : 1/(2:ℝ)^(q+5)=(1/(2:ℝ)^q)/32 := by rw [pow_add]; norm_num; ring
  have hq2 : 1/(2:ℝ)^(q+2)=(1/(2:ℝ)^q)/4 := by rw [pow_add]; norm_num; ring
  have hunit : 1/(2:ℝ)^P≤(1/(2:ℝ)^q)/16 := by
    calc
      _ ≤ 1/(2:ℝ)^(q+4) := one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by norm_num) (show q+4≤P by omega))
      _ = (1/(2:ℝ)^q)/16 := by rw [pow_add]; norm_num; ring
  apply runs_start_le
  unfold negativePowerBody
  refine runs_seq_call_le hlC (vs:=[a,one,L,P,E,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,_,_,rfl,hP,by omega,by omega,hPw',ha,ho,hva,hvo,hone,hlo,hhi⟩,
      hz,by change heap+logarithmSpace L P E<2^w; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨⟨hlo₁,hhi₁,hf₁,hz₁,_⟩,hvalid₁,herr₁⟩
    change heap≤v₁ at hlo₁
    change v₁≤heap+logarithmSpace L P E at hhi₁
    change (∀ z<heap,mem₁ z=mem z) at hf₁
    change Valid mem₁ (v₁-L) h L at hvalid₁
    change |fixVal mem₁ (v₁-L) h L P-Real.log (fixVal mem a h L P)|≤1/(2:ℝ)^(q+5) at herr₁
    have hlog1 : |fixVal mem₁ (v₁-L) h L P-Real.log (fixVal mem a h L P)|≤1 := by
      rw [hq5] at herr₁
      linarith only [herr₁,hε1]
    have hvd₁ := valid_frozen hf₁ hd hvd
    have hd₁ : intVal mem₁ d h L=intVal mem d h L := value_frozen hf₁ hd
    have hdfix₁ : fixVal mem₁ d h L P=fixVal mem d h L P := by simp only [fixVal,hd₁]
    have hprodBound := negative_power_product_bound (P:=P) hlo hhi hd0 hd2 hlog1
    have hprodBound' : |dyadicFloor P (fixVal mem₁ d h L P*fixVal mem₁ (v₁-L) h L P)|≤2*(E:ℝ)+3 := by
      rw [hdfix₁]
      exact hprodBound
    obtain ⟨hprodFit,hnegFit⟩ := negative_power_product_fits (h:=h) (L:=L) (E:=E)
      (show P+E+6≤h*L by omega) hprodBound'
    have hv₁w : v₁<2^w := by omega
    have hptr₁w : v₁-L<2^w := by omega
    refine runs_seq_call_le hmC (vs:=[d,v₁-L,L,P,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,_,_,rfl,hP,by omega,by omega,hvd₁,hvalid₁⟩,
        hz₁,by change v₁+(11*L+1)<2^w; omega⟩
    · intro v₂ mem₂ pos₂ hp₂
      rcases hp₂ with ⟨hv₂,_,_,hf₂,hz₂,hvalid₂,hvalue₂⟩
      change v₂=v₁+(11*L+1) at hv₂
      change (∀ z<v₁,mem₂ z=mem₁ z) at hf₂
      change Valid mem₂ (v₁+10*L+1) h L at hvalid₂
      change intVal mem₂ (v₁+10*L+1) h L=wrap h L
        (intVal mem₁ d h L*intVal mem₁ (v₁-L) h L/(2:ℤ)^P) at hvalue₂
      have hptr₂ : v₁+10*L+1=v₂-L := by omega
      rw [hptr₂,wrap_of_fits hprodFit] at hvalue₂
      rw [hptr₂] at hvalid₂
      have hv₂w : v₂<2^w := by omega
      have hptr₂w : v₂-L<2^w := by omega
      refine runs_seq_call_le hnC (vs:=[v₂-L,L,v₂]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨_,_,_,rfl,⟨⟨_,_,_,_,rfl,by omega,by omega,hvalid₂⟩,
          hz₂,by change v₂+L<2^w; omega⟩⟩
      · intro v₃ mem₃ pos₃ hp₃
        rcases hp₃ with ⟨hv₃,_,_,hf₃,hz₃,hlist₃⟩
        change v₃=v₂+L at hv₃
        change (∀ z<v₂,mem₃ z=mem₂ z) at hf₃
        change ListAt mem₃ v₂ (digits h L (capacity h L-1-unsignedVal mem₂ (v₂-L) h L+1)) at hlist₃
        obtain ⟨hvalid₃,hvalue₃⟩ := negateCarry_value_one hvalid₂ hlist₃
        rw [hvalue₂,wrap_of_fits hnegFit] at hvalue₃
        have hproduct : fixVal mem₃ v₂ h L P=
            -dyadicFloor P (fixVal mem d h L P*fixVal mem₁ (v₁-L) h L P) := by
          rw [fixVal,hvalue₃,Int.cast_neg,neg_div]
          rw [← dyadicFloor_product]
          rw [← hdfix₁]
          rfl
        have hBarg : |fixVal mem₃ v₂ h L P|≤(2*E+4:ℕ) := by
          rw [hproduct,abs_neg]
          push_cast
          linarith only [hprodBound]
        have hproductError : |fixVal mem₃ v₂ h L P-(-fixVal mem d h L P*fixVal mem₁ (v₁-L) h L P)|≤
            (1/(2:ℝ)^q)/16 := by
          rw [hproduct]
          exact le_trans (negative_power_product_rounding P _ _) hunit
        have hvo₃ := valid_frozen hf₃ (by omega)
          (valid_frozen hf₂ (by omega) (valid_frozen hf₁ ho hvo))
        have hone₃ : intVal mem₃ one h L=(2:ℤ)^P :=
          (value_frozen hf₃ (by omega)).trans ((value_frozen hf₂ (by omega)).trans
            ((value_frozen hf₁ ho).trans hone))
        have hv₃w : v₃<2^w := by omega
        have hptr₃ : v₃-L=v₂ := by omega
        refine runs_seq_call_le heC (vs:=[v₃-L,one,L,P,2*E+4,v₃]) (by eval_expr) (by wram_words) ?_ ?_
        · refine ⟨⟨_,_,_,_,_,_,rfl,hP,by omega,by omega,hPw',by omega,by omega,?_,hvo₃,hone₃,?_⟩,
            hz₃,by change v₃+exponentialSpace L P (2*E+4)<2^w; omega⟩
          · rw [hptr₃]; exact hvalid₃
          · rw [hptr₃]; exact hBarg
        · intro v mem₄ pos₄ hp₄
          rcases hp₄ with ⟨⟨hlo₄,hhi₄,hf₄,hz₄,_⟩,hvalid₄,herr₄⟩
          change v₃≤v at hlo₄
          change v≤v₃+exponentialSpace L P (2*E+4) at hhi₄
          change (∀ z<v₃,mem₄ z=mem₃ z) at hf₄
          change Valid mem₄ (v-L) h L at hvalid₄
          change |fixVal mem₄ (v-L) h L P-Real.exp (fixVal mem₃ (v₃-L) h L P)|≤
            (1/(2:ℝ)^(q+2))*Real.exp (fixVal mem₃ (v₃-L) h L P) at herr₄
          rw [hptr₃] at herr₄
          have herr := negative_power_relative_error hxpos hd0 hd2 hε0 hε1
            (by simpa only [hq5] using herr₁) hproductError (by simpa only [hq2] using herr₄)
          have hvw : v<2^w := by omega
          refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
          · change (heap≤v ∧ v≤heap+negativePowerSpace L P E ∧ (∀ z<heap,mem₄ z=mem z) ∧
              ZeroFrom mem₄ v ∧ True) ∧ Valid mem₄ (v-L) h L ∧
              |fixVal mem₄ (v-L) h L P-Real.rpow (fixVal mem a h L P) (-fixVal mem d h L P)|≤
                (1/(2:ℝ)^q)*Real.rpow (fixVal mem a h L P) (-fixVal mem d h L P)
            refine ⟨⟨by omega,?_,?_,hz₄,trivial⟩,hvalid₄,herr⟩
            · unfold negativePowerSpace; omega
            · intro z hz
              exact (hf₄ z (by omega)).trans ((hf₃ z (by omega)).trans
                ((hf₂ z (by omega)).trans (hf₁ z hz)))
          · simp only [negativePowerContract,logarithmContract,fixedMultiplyContract,negateContract,
              negateCarryContract,negateArgs,exponentialContract,heapContract,List.getD_cons_zero,
              List.getD_cons_succ,Expr.size_reg,Expr.size_bin,Expr.size_const,argsSize_cons,argsSize_nil,
              negativePowerCost]
            ring_nf
            omega

end MinCostFlow.Num
