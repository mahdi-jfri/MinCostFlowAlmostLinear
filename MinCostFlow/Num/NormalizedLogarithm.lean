module

public import MinCostFlow.Num.NormalizedLogarithmIntegerFacts
public import MinCostFlow.Num.LogHorner
public import MinCostFlow.Num.Subtract
public import MinCostFlow.Num.FixedDivide
public import MinCostFlow.Num.ShiftLeft
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Fixed-point logarithm on the normalized interval

For an input in `[1,2]`, form `(x-1)/(x+1)`, round its square, evaluate
the odd series by Horner's rule, and multiply by twice the argument. All
intermediates are bounded and every rounding is reflected in the integer
formula. The real error bound follows from the separate analysis lemmas.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Space for the normalized logarithm, including its Horner workspace. -/
def normalizedLogarithmSpace (L n : ℕ) : ℕ :=
  26*L+2+fixedDivideSpace L+logHornerSpace L n

/-- Arguments `[x,one,L,P,n,heap]`. -/
def normalizedLogarithmBody (sub add divide mul horner shift : ℕ) : Stmt :=
  .call 6 sub [.reg 0,.reg 1,.reg 2,.reg 5] ;;
  .call 7 add [.reg 0,.reg 1,.reg 2,.const 0,.reg 6] ;;
  .call 8 divide [.bin .sub (.reg 6) (.reg 2),.bin .sub (.reg 7) (.reg 2),
    .reg 2,.reg 3,.reg 7] ;;
  .call 9 mul [.bin .sub (.reg 8) (.reg 2),.bin .sub (.reg 8) (.reg 2),
    .reg 2,.reg 3,.reg 8] ;;
  .call 10 horner [.bin .sub (.reg 9) (.reg 2),.reg 1,.reg 2,.reg 3,
    .const 0,.reg 4,.reg 9] ;;
  .call 11 mul [.bin .sub (.reg 8) (.reg 2),.bin .sub (.reg 10) (.reg 2),
    .reg 2,.reg 3,.reg 10] ;;
  .call 12 shift [.bin .sub (.reg 11) (.reg 2),.reg 2,.const 1,.reg 11] ;;
  .ret (.reg 12)

/-- The normalized logarithm with all arithmetic dependencies. -/
def normalizedLogarithmModule (b h : ℕ) : List Stmt :=
  [normalizedLogarithmBody (b+1) (b+6) (b+7) (b+39) (b+50) (b+89)] ++
    (subtractModule (b+1) h ++ (addCarryModule (b+6) h ++
      (fixedDivideModule (b+7) h ++ (fixedMultiplyModule (b+39) h ++
        (logHornerModule (b+50) h ++ shiftLeftModule (b+89) h)))))

/-- Exact integer specification of normalized logarithm evaluation. The
series length is `n`. The input value lies in `[1,2]`. -/
def normalizedLogarithmContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a one L P n heap,args=[a,one,L,P,n,heap] ∧ h∣P ∧
      P+4≤h*L ∧ a+L≤heap ∧ one+L≤heap ∧ Valid mem a h L ∧ Valid mem one h L ∧
      intVal mem one h L=(2:ℤ)^P ∧ (2:ℤ)^P≤ intVal mem a h L ∧
      intVal mem a h L≤2*(2:ℤ)^P ∧ 2*n+1≤2^P ∧ 2*n+1<2^w)
    (fun args mem mem' =>
      Valid mem' (heapArg args+normalizedLogarithmSpace (args.getD 2 0) (args.getD 4 0)-args.getD 2 0)
        h (args.getD 2 0) ∧
      intVal mem' (heapArg args+normalizedLogarithmSpace (args.getD 2 0) (args.getD 4 0)-args.getD 2 0)
        h (args.getD 2 0)=normalizedLogInt (args.getD 3 0)
          (intVal mem (args.getD 0 0) h (args.getD 2 0)) (args.getD 4 0))
    (fun args _ => args.getD 4 0*(500*(args.getD 2 0)^2+2000*args.getD 2 0+2000)+
      5000*(args.getD 2 0)^2+10000*args.getD 2 0+10000)
    (fun args _ => normalizedLogarithmSpace (args.getD 2 0) (args.getD 4 0))
  { C with post := fun args mem v mem' =>
    v=heapArg args+normalizedLogarithmSpace (args.getD 2 0) (args.getD 4 0) ∧ C.post args mem v mem' }

/-- The normalized logarithm uses no random statement. -/
theorem normalizedLogarithmModule_noRand (b h : ℕ) :
    ∀ s∈normalizedLogarithmModule b h,s.NoRand := by
  intro s hs
  simp only [normalizedLogarithmModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hsub | ha | hd | hm | hh | hshift
  · simp [normalizedLogarithmBody,Stmt.NoRand]
  · exact subtractModule_noRand _ _ _ hsub
  · have he : s=addCarryBody (b+6) h := by simpa [addCarryModule] using ha
    subst s
    exact addCarryBody_noRand _ _
  · exact fixedDivideModule_noRand _ _ _ hd
  · exact fixedMultiplyModule_noRand _ _ _ hm
  · exact logHornerModule_noRand _ _ _ hh
  · exact shiftLeftModule_noRand _ _ _ hshift

private theorem valid_frozen {mem mem' : ℕ→ℕ} {a h L heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) (hv : Valid mem a h L) :
    Valid mem' a h L := by
  intro i hi
  rw [hf _ (by omega)]
  exact hv i hi

private theorem value_frozen {mem mem' : ℕ→ℕ} {a h L heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) :
    intVal mem' a h L=intVal mem a h L := intVal_congr (fun i hi => hf _ (by omega))

set_option maxHeartbeats 600000 in
/-- Every intermediate of the normalized logarithm fits. The procedure
therefore computes exactly its rounded integer formula and respects the stated
heap and polynomial cost bounds. -/
theorem normalizedLogarithm_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (normalizedLogarithmModule b h)) :
    MeetsContract w p b (normalizedLogarithmContract w h) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hsub := hasAt_append_left ht
  have ht₂ := hasAt_append_right ht
  change p.HasAt (b+6) _ at ht₂
  have hadd := hasAt_append_left ht₂
  have ht₃ := hasAt_append_right ht₂
  change p.HasAt (b+7) _ at ht₃
  have hdiv := hasAt_append_left ht₃
  have ht₄ := hasAt_append_right ht₃
  change p.HasAt (b+39) _ at ht₄
  have hmul := hasAt_append_left ht₄
  have ht₅ := hasAt_append_right ht₄
  change p.HasAt (b+50) _ at ht₅
  have hhorner := hasAt_append_left ht₅
  have hshift := hasAt_append_right ht₅
  change p.HasAt (b+89) _ at hshift
  have hsubC := subtract_meetsContract hh (show 2*h+2≤w by omega) hsub
  have haddC := addCarry_meetsContract hh (show 2*h+2≤w by omega) hadd
  have hdivC := fixedDivide_meetsContract hh hw hdiv
  have hmulC := fixedMultiply_meetsContract hh (show 2*h+2≤w by omega) hmul
  have hhornerC := logHorner_meetsContract hh hw hhorner
  have hshiftC := shiftLeft_meetsContract hh (show 2*h+2≤w by omega) hshift
  have hw1 : 1<2^w := by
    have hb := base_lt_word (show 2*h+2≤w by omega)
    exact lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a,one,L,P,n,heap,rfl,hP,hwidth,ha,ho,hva,hvo,hone,hlo,hhi,hden,hdenw⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+normalizedLogarithmSpace L n<2^w at hbound
  unfold normalizedLogarithmSpace at hbound
  set N := intVal mem a h L
  have hN0 : (2:ℤ)^P≤N := hlo
  have hN1 : N≤2*(2:ℤ)^P := hhi
  have hscale : (0:ℤ)<(2:ℤ)^P := pow_pos (by decide) _
  obtain ⟨⟨hT0,hT1⟩,⟨hS0,hS1⟩,hZ0,hZ1⟩ := normalizedLogInt_bounds hN0 hN1 n
  obtain ⟨hH0,hH1⟩ := logHornerInt_bounds hS0 hS1 0 n
  have hT2 : 2*normalizedLogArgument P N≤(2:ℤ)^P := by omega
  obtain ⟨hM0,hM1⟩ := logHornerInt_product_bounds hT0 hT2 hH0 hH1
  have hsubfit : Fits h L (N-(2:ℤ)^P) := fits_four_scale hwidth (by omega) (by omega)
  have haddfit : Fits h L (N+(2:ℤ)^P) := fits_four_scale hwidth (by omega) (by omega)
  have hTfit : Fits h L (normalizedLogArgument P N) := fits_twice_scale hwidth hT0 (by omega)
  have hSfit : Fits h L (normalizedLogSquare P N) := fits_twice_scale hwidth hS0 (by omega)
  have hMfit : Fits h L (normalizedLogArgument P N*
      logHornerInt P (normalizedLogSquare P N) 0 n/(2:ℤ)^P) :=
    fits_twice_scale hwidth hM0 (by omega)
  have hZfit : Fits h L (normalizedLogInt P N n) := fits_twice_scale hwidth hZ0 hZ1
  have hF : L≤fixedDivideSpace L := by unfold fixedDivideSpace; omega
  have hH : L≤logHornerSpace L n := by unfold logHornerSpace; omega
  have haw : a<2^w := hwords a (by simp)
  have how : one<2^w := hwords one (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPw : P<2^w := hwords P (by simp)
  have hnw : n<2^w := hwords n (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  apply runs_start_le
  unfold normalizedLogarithmBody
  refine runs_seq_call_le hsubC (vs:=[a,one,L,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,rfl,ha,ho,hva,hvo⟩,hz,by change heap+2*L<2^w; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨hv₁,_,_,hf₁,hz₁,hvalid₁,hvalue₁⟩
    change v₁=heap+2*L at hv₁
    change (∀ z<heap,mem₁ z=mem z) at hf₁
    change Valid mem₁ (heap+L) h L at hvalid₁
    change intVal mem₁ (heap+L) h L=wrap h L (N-intVal mem one h L) at hvalue₁
    rw [hone,wrap_of_fits hsubfit] at hvalue₁
    have hptr₁ : heap+L=v₁-L := by omega
    rw [hptr₁] at hvalid₁ hvalue₁
    have hva₁ : Valid mem₁ a h L := valid_frozen hf₁ ha hva
    have hvo₁ : Valid mem₁ one h L := valid_frozen hf₁ ho hvo
    have ha₁ : intVal mem₁ a h L=N := value_frozen hf₁ ha
    have ho₁ : intVal mem₁ one h L=(2:ℤ)^P := (value_frozen hf₁ ho).trans hone
    have hv₁w : v₁<2^w := by omega
    have hptr₁w : v₁-L<2^w := by omega
    refine runs_seq_call_le haddC (vs:=[a,one,L,0,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,_,_,rfl,by omega,by omega,by omega,hva₁,hvo₁⟩,
        hz₁,by change v₁+L<2^w; omega⟩
    · intro v₂ mem₂ pos₂ hp₂
      rcases hp₂ with ⟨hv₂,_,_,hf₂,hz₂,hlist₂⟩
      change v₂=v₁+L at hv₂
      change (∀ z<v₁,mem₂ z=mem₁ z) at hf₂
      change ListAt mem₂ v₁ (digits h L (unsignedVal mem₁ a h L+unsignedVal mem₁ one h L+0)) at hlist₂
      have hvalid₂ := (addCarry_value hlist₂).1
      have hsumfit : Fits h L (intVal mem₁ a h L+intVal mem₁ one h L+(0:ℕ)) := by
        simpa only [ha₁,ho₁,Nat.cast_zero,add_zero] using haddfit
      have hvalue₂ := addCarry_value_of_fits hlist₂ hsumfit
      rw [ha₁,ho₁] at hvalue₂
      simp only [Nat.cast_zero,add_zero] at hvalue₂
      have hptr₂ : v₁=v₂-L := by omega
      rw [hptr₂] at hvalid₂ hvalue₂
      have hvsub₂ : Valid mem₂ (v₁-L) h L := valid_frozen hf₂ (by omega) hvalid₁
      have hsub₂ : intVal mem₂ (v₁-L) h L=N-(2:ℤ)^P :=
        (value_frozen hf₂ (by omega)).trans hvalue₁
      have hv₂w : v₂<2^w := by omega
      have hptr₂w : v₂-L<2^w := by omega
      have hquotfit : Fits h L (floorDiv
          (intVal mem₂ (v₁-L) h L*(2:ℤ)^P) (intVal mem₂ (v₂-L) h L)) := by
        rw [hsub₂,hvalue₂,floorDiv,ite_eq_right (by omega)]
        exact hTfit
      refine runs_seq_call_le hdivC (vs:=[v₁-L,v₂-L,L,P,v₂]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨_,_,_,_,_,rfl,hP,by omega,by omega,hvsub₂,hvalid₂,
          by rw [hvalue₂]; omega,hquotfit⟩,hz₂,by change v₂+fixedDivideSpace L<2^w; omega⟩
      · intro v₃ mem₃ pos₃ hp₃
        rcases hp₃ with ⟨hv₃,_,_,hf₃,hz₃,hvalid₃,hvalue₃⟩
        change v₃=v₂+fixedDivideSpace L at hv₃
        change (∀ z<v₂,mem₃ z=mem₂ z) at hf₃
        change Valid mem₃ (v₂+9*L+integerDivideSpace (3*L)) h L at hvalid₃
        change intVal mem₃ (v₂+9*L+integerDivideSpace (3*L)) h L=
          floorDiv (intVal mem₂ (v₁-L) h L*(2:ℤ)^P) (intVal mem₂ (v₂-L) h L) at hvalue₃
        have hptr₃ : v₂+9*L+integerDivideSpace (3*L)=v₃-L := by
          unfold fixedDivideSpace at hv₃; omega
        rw [hptr₃] at hvalid₃ hvalue₃
        rw [hsub₂,hvalue₂,floorDiv,ite_eq_right (by omega)] at hvalue₃
        change intVal mem₃ (v₃-L) h L=normalizedLogArgument P N at hvalue₃
        have hv₃w : v₃<2^w := by omega
        have hptr₃w : v₃-L<2^w := by omega
        refine runs_seq_call_le hmulC (vs:=[v₃-L,v₃-L,L,P,v₃]) (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨⟨_,_,_,_,_,rfl,hP,by omega,by omega,hvalid₃,hvalid₃⟩,
            hz₃,by change v₃+(11*L+1)<2^w; omega⟩
        · intro v₄ mem₄ pos₄ hp₄
          rcases hp₄ with ⟨hv₄,_,_,hf₄,hz₄,hvalid₄,hvalue₄⟩
          change v₄=v₃+(11*L+1) at hv₄
          change (∀ z<v₃,mem₄ z=mem₃ z) at hf₄
          change Valid mem₄ (v₃+10*L+1) h L at hvalid₄
          change intVal mem₄ (v₃+10*L+1) h L=wrap h L
            (intVal mem₃ (v₃-L) h L*intVal mem₃ (v₃-L) h L/(2:ℤ)^P) at hvalue₄
          have hptr₄ : v₃+10*L+1=v₄-L := by omega
          rw [hptr₄,hvalue₃] at hvalue₄
          rw [hptr₄] at hvalid₄
          change intVal mem₄ (v₄-L) h L=wrap h L (normalizedLogSquare P N) at hvalue₄
          rw [wrap_of_fits hSfit] at hvalue₄
          have hvo₄ : Valid mem₄ one h L := valid_frozen hf₄ (by omega)
            (valid_frozen hf₃ (by omega) (valid_frozen hf₂ (by omega) hvo₁))
          have ho₄ : intVal mem₄ one h L=(2:ℤ)^P :=
            (value_frozen hf₄ (by omega)).trans
              ((value_frozen hf₃ (by omega)).trans ((value_frozen hf₂ (by omega)).trans ho₁))
          have hv₄w : v₄<2^w := by omega
          have hptr₄w : v₄-L<2^w := by omega
          refine runs_seq_call_le hhornerC (vs:=[v₄-L,one,L,P,0,n,v₄])
            (by eval_expr) (by wram_words) ?_ ?_
          · refine ⟨⟨_,_,_,_,_,_,_,rfl,hP,hwidth,by omega,by omega,hvalid₄,hvo₄,ho₄,?_,?_,?_,?_⟩,
              hz₄,by change v₄+logHornerSpace L n<2^w; omega⟩
            · rw [hvalue₄]; exact hS0
            · rw [hvalue₄]; exact hS1
            · simpa only [zero_add] using hden
            · simpa only [zero_add] using hdenw
          · intro v₅ mem₅ pos₅ hp₅
            rcases hp₅ with ⟨hv₅,_,_,hf₅,hz₅,hvalid₅,hvalue₅⟩
            change v₅=v₄+logHornerSpace L n at hv₅
            change (∀ z<v₄,mem₅ z=mem₄ z) at hf₅
            change Valid mem₅ (v₄+logHornerSpace L n-L) h L at hvalid₅
            change intVal mem₅ (v₄+logHornerSpace L n-L) h L=
              logHornerInt P (intVal mem₄ (v₄-L) h L) 0 n at hvalue₅
            rw [← hv₅,hvalue₄] at hvalue₅
            rw [← hv₅] at hvalid₅
            have hvt₅ : Valid mem₅ (v₃-L) h L :=
              valid_frozen hf₅ (by omega) (valid_frozen hf₄ (by omega) hvalid₃)
            have ht₅ : intVal mem₅ (v₃-L) h L=normalizedLogArgument P N :=
              (value_frozen hf₅ (by omega)).trans ((value_frozen hf₄ (by omega)).trans hvalue₃)
            have hv₅w : v₅<2^w := by omega
            have hptr₅w : v₅-L<2^w := by omega
            refine runs_seq_call_le hmulC (vs:=[v₃-L,v₅-L,L,P,v₅]) (by eval_expr) (by wram_words) ?_ ?_
            · exact ⟨⟨_,_,_,_,_,rfl,hP,by omega,by omega,hvt₅,hvalid₅⟩,
                hz₅,by change v₅+(11*L+1)<2^w; omega⟩
            · intro v₆ mem₆ pos₆ hp₆
              rcases hp₆ with ⟨hv₆,_,_,hf₆,hz₆,hvalid₆,hvalue₆⟩
              change v₆=v₅+(11*L+1) at hv₆
              change (∀ z<v₅,mem₆ z=mem₅ z) at hf₆
              change Valid mem₆ (v₅+10*L+1) h L at hvalid₆
              change intVal mem₆ (v₅+10*L+1) h L=wrap h L
                (intVal mem₅ (v₃-L) h L*intVal mem₅ (v₅-L) h L/(2:ℤ)^P) at hvalue₆
              have hptr₆ : v₅+10*L+1=v₆-L := by omega
              rw [hptr₆,ht₅,hvalue₅,wrap_of_fits hMfit] at hvalue₆
              rw [hptr₆] at hvalid₆
              have hv₆w : v₆<2^w := by omega
              have hptr₆w : v₆-L<2^w := by omega
              refine runs_seq_call_le hshiftC (vs:=[v₆-L,L,1,v₆]) (by eval_expr) (by wram_words) ?_ ?_
              · exact ⟨⟨_,_,_,_,rfl,by omega,hvalid₆⟩,hz₆,by change v₆+L<2^w; omega⟩
              · intro v mem₇ pos₇ hp₇
                rcases hp₇ with ⟨hv,_,_,hf₇,hz₇,hvalid₇,hvalue₇⟩
                change v=v₆+L at hv
                change (∀ z<v₆,mem₇ z=mem₆ z) at hf₇
                change Valid mem₇ v₆ h L at hvalid₇
                change intVal mem₇ v₆ h L=wrap h L (intVal mem₆ (v₆-L) h L*(2:ℤ)^1) at hvalue₇
                rw [hvalue₆,pow_one] at hvalue₇
                have hez : (normalizedLogArgument P N*logHornerInt P (normalizedLogSquare P N) 0 n/
                    (2:ℤ)^P)*2=normalizedLogInt P N n := by unfold normalizedLogInt; ring
                rw [hez,wrap_of_fits hZfit] at hvalue₇
                have hvw : v<2^w := by omega
                refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
                · change v=heap+normalizedLogarithmSpace L n ∧ heap≤v ∧
                    v≤heap+normalizedLogarithmSpace L n ∧ (∀ z<heap,mem₇ z=mem z) ∧
                    ZeroFrom mem₇ v ∧ Valid mem₇ (heap+normalizedLogarithmSpace L n-L) h L ∧
                    intVal mem₇ (heap+normalizedLogarithmSpace L n-L) h L=normalizedLogInt P N n
                  have he : v=heap+normalizedLogarithmSpace L n := by unfold normalizedLogarithmSpace; omega
                  have hout : heap+normalizedLogarithmSpace L n-L=v₆ := by rw [← he]; omega
                  refine ⟨he,by omega,by omega,?_,hz₇,?_,?_⟩
                  · intro z hz
                    exact (hf₇ z (by omega)).trans ((hf₆ z (by omega)).trans ((hf₅ z (by omega)).trans
                      ((hf₄ z (by omega)).trans ((hf₃ z (by omega)).trans
                        ((hf₂ z (by omega)).trans (hf₁ z hz))))))
                  · rw [hout]; exact hvalid₇
                  · rw [hout]; exact hvalue₇
                · simp only [normalizedLogarithmContract,subtractContract,addCarryContract,
                    fixedDivideContract,fixedMultiplyContract,logHornerContract,shiftLeftContract,
                    heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,
                    Expr.size_bin,Expr.size_const,argsSize_cons,argsSize_nil]
                  ring_nf
                  omega

/-- The actual output block of a normalized logarithm run has absolute
error at most `2⁻q` when the series has `q+4` terms and ten guard bits. -/
theorem normalizedLogarithm_output_error {w h a one L P q heap v : ℕ}
    {mem mem' : ℕ→ℕ}
    (hpre : (normalizedLogarithmContract w h).pre [a,one,L,P,q+4,heap] mem)
    (hpost : (normalizedLogarithmContract w h).post [a,one,L,P,q+4,heap] mem v mem')
    (hP : q+10≤P) :
    |fixVal mem' (v-L) h L P-Real.log (fixVal mem a h L P)|≤1/(2:ℝ)^q := by
  rcases hpre.1 with ⟨a',one',L',P',n',heap',he,_,_,_,_,_,_,_,hlo,hhi,_,_⟩
  simp only [List.cons.injEq,and_true] at he
  rcases he with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  rcases hpost with ⟨hv,_,_,_,_,_,hval⟩
  change v=heap+normalizedLogarithmSpace L (q+4) at hv
  change intVal mem' (heap+normalizedLogarithmSpace L (q+4)-L) h L=
    normalizedLogInt P (intVal mem a h L) (q+4) at hval
  rw [hv]
  change |(intVal mem' (heap+normalizedLogarithmSpace L (q+4)-L) h L:ℝ)/(2:ℝ)^P-
    Real.log (fixVal mem a h L P)|≤_
  rw [hval,normalizedLogInt_value hlo]
  have hp : (0:ℝ)<(2:ℝ)^P := by positivity
  apply normalized_log_error (P:=P) (q:=q) ?_ ?_ hP
  · apply (le_div_iff₀ hp).mpr
    simpa only [one_mul] using (show (2:ℝ)^P≤(intVal mem a h L:ℝ) by exact_mod_cast hlo)
  · apply (div_le_iff₀ hp).mpr
    exact_mod_cast hhi

end MinCostFlow.Num
