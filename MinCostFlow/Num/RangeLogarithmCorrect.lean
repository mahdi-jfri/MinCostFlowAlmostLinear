module

public import MinCostFlow.Num.RangeLogarithm
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Correctness of logarithm range reduction

The reduction count decreases whenever a shift is needed. The integer range
bounds justify each recursive call. Signed range bounds ensure that correcting
by the stored logarithm of two never wraps. The normalized branch uses the
verified series procedure.
-/

public section
namespace MinCostFlow.Num
open WordRAM

private theorem valid_frozen {mem mem' : ℕ→ℕ} {a h L heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) (hv : Valid mem a h L) :
    Valid mem' a h L := by
  intro i hi
  rw [hf _ (by omega)]
  exact hv i hi

private theorem value_frozen {mem mem' : ℕ→ℕ} {a h L heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) :
    intVal mem' a h L=intVal mem a h L := intVal_congr (fun i hi => hf _ (by omega))

private theorem range_space_step (L P E : ℕ) :
    rangeLogarithmSpace L P (E+1)=rangeLogarithmSpace L P E+(3*L+1) := by
  unfold rangeLogarithmSpace
  ring

set_option maxHeartbeats 600000 in
/-- Range reduction meets its integer specification and heap contract for every
random tape, with explicit polynomial cost and space. -/
theorem rangeLogarithm_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (rangeLogarithmModule b h)) :
    MeetsContract w p b (rangeLogarithmContract w h) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hl := hasAt_append_left ht
  have ht₂ := hasAt_append_right ht
  change p.HasAt (b+4) _ at ht₂
  have hleft := hasAt_append_left ht₂
  have ht₃ := hasAt_append_right ht₂
  change p.HasAt (b+6) _ at ht₃
  have hright := hasAt_append_left ht₃
  have ht₄ := hasAt_append_right ht₃
  change p.HasAt (b+10) _ at ht₄
  have hsub := hasAt_append_left ht₄
  have ht₅ := hasAt_append_right ht₄
  change p.HasAt (b+15) _ at ht₅
  have hadd := hasAt_append_left ht₅
  have hnorm := hasAt_append_right ht₅
  change p.HasAt (b+16) _ at hnorm
  have hb := base_lt_word (show 2*h+2≤w by omega)
  have hw1 : 1<2^w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  have hw0 : w≠0 := by omega
  have hlC := less_meetsContract hh hw1 hb hl
  have hleftC := shiftLeft_meetsContract hh (show 2*h+2≤w by omega) hleft
  have hrightC := shiftRight_meetsContract hh hw1 hb hright
  have hsubC := subtract_meetsContract hh (show 2*h+2≤w by omega) hsub
  have haddC := addCarry_meetsContract hh (show 2*h+2≤w by omega) hadd
  have hnormC := normalizedLogarithm_meetsContract hh hw hnorm
  apply meetsContract_of_rec (fun args _ => args.getD 6 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨⟨a,one,two,c,L,P,E,heap,rfl,hP,hP10,hwidth,hPw',ha,ho,ht,hc,
    hva,hvo,hvt,hvc,hone,htwo,hC0,hC1,hlo,hhi⟩,hz,hbound⟩
  change E=k at hk
  subst k
  change ZeroFrom mem heap at hz
  change heap+rangeLogarithmSpace L P E<2^w at hbound
  set N := intVal mem a h L
  set C := intVal mem c h L
  have hNlo : (2:ℤ)^P≤(2:ℤ)^E*N := hlo
  have hNhi : N≤(2:ℤ)^(E+1)*(2:ℤ)^P := hhi
  have hscale : (0:ℤ)<(2:ℤ)^P := by positivity
  have hNpos : 0<N := by
    by_contra hn
    have hm := mul_nonpos_of_nonneg_of_nonpos (show (0:ℤ)≤(2:ℤ)^E by positivity)
      (show N≤0 by omega)
    omega
  have hfit := fits_log_range hwidth (rangeLogInt_bounds hC0 hC1 E N hNlo hNhi)
  have hnormSpace : L≤normalizedLogarithmSpace L (P+4) := by unfold normalizedLogarithmSpace; omega
  have hspace : L≤rangeLogarithmSpace L P E := by unfold rangeLogarithmSpace; omega
  have haw : a<2^w := hwords a (by simp)
  have how : one<2^w := hwords one (by simp)
  have htw : two<2^w := hwords two (by simp)
  have hcw : c<2^w := hwords c (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPw : P<2^w := hwords P (by simp)
  have hEw : E<2^w := hwords E (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have hP4w : P+4<2^w := by omega
  apply runs_start_le
  unfold rangeLogarithmBody
  refine runs_seq_call_le hlC (vs:=[a,one,L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨_,_,_,rfl,by omega,by omega,hva,hvo⟩
  · intro flag mem₀ pos₀ hp₀
    rcases hp₀ with ⟨hmem,hflag⟩
    change mem₀=mem at hmem
    subst mem₀
    change flag=(if N< intVal mem one h L then 1 else 0) at hflag
    rw [hone] at hflag
    wram_step
    · have hflagpos : flag≠0 := by simpa [startState] using hcond
      have hsmall : N<(2:ℤ)^P := by
        by_contra he
        rw [ite_eq_right he] at hflag
        exact hflagpos hflag
      have hE0 : E≠0 := by
        intro he
        rw [he,pow_zero,one_mul] at hNlo
        omega
      obtain ⟨E,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hE0
      rw [range_space_step] at hbound
      obtain ⟨hlo',hhi'⟩ := log_range_double hNlo hsmall
      have hleftfit : Fits h L (N*2) :=
        fits_four_scale (show P+4≤h*L by omega) (by omega) (by omega)
      have hEmw : E<2^w := by omega
      refine runs_seq_call_le hleftC (vs:=[a,L,1,heap]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨_,_,_,_,rfl,ha,hva⟩,hz,by change heap+L<2^w; omega⟩
      · intro v₁ mem₁ pos₁ hp₁
        rcases hp₁ with ⟨hv₁,_,_,hf₁,hz₁,hvalid₁,hvalue₁⟩
        change v₁=heap+L at hv₁
        change (∀ z<heap,mem₁ z=mem z) at hf₁
        change Valid mem₁ heap h L at hvalid₁
        change intVal mem₁ heap h L=wrap h L (N*(2:ℤ)^1) at hvalue₁
        rw [pow_one,wrap_of_fits hleftfit] at hvalue₁
        have hptr₁ : heap=v₁-L := by omega
        rw [hptr₁] at hvalid₁ hvalue₁
        have hvo₁ := valid_frozen hf₁ ho hvo
        have hvt₁ := valid_frozen hf₁ ht hvt
        have hvc₁ := valid_frozen hf₁ hc hvc
        have hone₁ : intVal mem₁ one h L=(2:ℤ)^P := (value_frozen hf₁ ho).trans hone
        have htwo₁ : intVal mem₁ two h L=2*(2:ℤ)^P := (value_frozen hf₁ ht).trans htwo
        have hC₁ : intVal mem₁ c h L=C := value_frozen hf₁ hc
        have hv₁w : v₁<2^w := by omega
        have hptr₁w : v₁-L<2^w := by omega
        have hrec : MeetsContract w p b
            ((rangeLogarithmContract w h).below (fun args _ => args.getD 6 0) (E+1)) := ih
        refine runs_seq_call_le hrec (vs:=[v₁-L,one,two,c,L,P,E,v₁])
          (by eval_expr <;> simp [Expr.eval,BinOp.eval,startState,hw0,hEmw]) (by wram_words) ?_ ?_
        · refine ⟨⟨⟨_,_,_,_,_,_,_,_,rfl,hP,hP10,by omega,hPw',by omega,by omega,by omega,by omega,
            hvalid₁,hvo₁,hvt₁,hvc₁,hone₁,htwo₁,?_,?_,?_,?_⟩,
            hz₁,by change v₁+rangeLogarithmSpace L P E<2^w; omega⟩,by change E<E+1; omega⟩
          · rw [hC₁]; exact hC0
          · rw [hC₁]; exact hC1
          · rw [hvalue₁]; nlinarith only [hlo']
          · rw [hvalue₁]; nlinarith only [hhi']
        · intro v₂ mem₂ pos₂ hp₂
          rcases hp₂ with ⟨⟨hlo₂,hhi₂,hf₂,hz₂,_⟩,hvalid₂,hvalue₂⟩
          change v₁≤v₂ at hlo₂
          change v₂≤v₁+rangeLogarithmSpace L P E at hhi₂
          change (∀ z<v₁,mem₂ z=mem₁ z) at hf₂
          change Valid mem₂ (v₂-L) h L at hvalid₂
          change intVal mem₂ (v₂-L) h L=
            rangeLogInt P (intVal mem₁ c h L) E (intVal mem₁ (v₁-L) h L) at hvalue₂
          rw [hC₁,hvalue₁] at hvalue₂
          have hmul : N*2=2*N := mul_comm _ _
          rw [hmul] at hvalue₂
          have hvc₂ := valid_frozen hf₂ (by omega) hvc₁
          have hC₂ : intVal mem₂ c h L=C := (value_frozen hf₂ (by omega)).trans hC₁
          have hv₂w : v₂<2^w := by omega
          have hptr₂w : v₂-L<2^w := by omega
          refine runs_seq_call_le hsubC (vs:=[v₂-L,c,L,v₂]) (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨⟨_,_,_,_,rfl,by omega,by omega,hvalid₂,hvc₂⟩,
              hz₂,by change v₂+2*L<2^w; omega⟩
          · intro v mem₃ pos₃ hp₃
            rcases hp₃ with ⟨hv,_,_,hf₃,hz₃,hvalid₃,hvalue₃⟩
            change v=v₂+2*L at hv
            change (∀ z<v₂,mem₃ z=mem₂ z) at hf₃
            change Valid mem₃ (v₂+L) h L at hvalid₃
            change intVal mem₃ (v₂+L) h L=wrap h L
              (intVal mem₂ (v₂-L) h L-intVal mem₂ c h L) at hvalue₃
            rw [hvalue₂,hC₂] at hvalue₃
            have he : rangeLogInt P C (E+1) N=rangeLogInt P C E (2*N)-C := by
              simp only [rangeLogInt,ite_eq_left hsmall]
            rw [← he,wrap_of_fits hfit] at hvalue₃
            have hout : v-L=v₂+L := by omega
            have hvw : v<2^w := by omega
            refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
            · change (heap≤v ∧ v≤heap+rangeLogarithmSpace L P (E+1) ∧
                (∀ z<heap,mem₃ z=mem z) ∧ ZeroFrom mem₃ v ∧ True) ∧
                Valid mem₃ (v-L) h L ∧ intVal mem₃ (v-L) h L=rangeLogInt P C (E+1) N
              refine ⟨⟨by omega,?_,?_,hz₃,trivial⟩,?_,?_⟩
              · rw [range_space_step]; omega
              · intro z hz
                exact (hf₃ z (by omega)).trans ((hf₂ z (by omega)).trans (hf₁ z hz))
              · rw [hout]; exact hvalid₃
              · rw [hout]; exact hvalue₃
            · simp only [rangeLogarithmContract,Contract.below,lessContract,shiftLeftContract,subtractContract,
                heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,
                Expr.size_const,argsSize_cons,argsSize_nil,rangeLogarithmCost,Nat.succ_eq_add_one]
              ring_nf
              omega
    · have hflagzero : flag=0 := by simpa [startState] using hcond
      have hnsmall : ¬N<(2:ℤ)^P := by
        intro he
        rw [ite_eq_left he] at hflag
        omega
      refine runs_seq_call_le hlC (vs:=[two,a,L]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨_,_,_,rfl,by omega,by omega,hvt,hva⟩
      · intro flag₂ mem₀ pos₁ hp₁
        rcases hp₁ with ⟨hmem,hflag₂⟩
        change mem₀=mem at hmem
        subst mem₀
        change flag₂=(if intVal mem two h L< intVal mem a h L then 1 else 0) at hflag₂
        rw [htwo] at hflag₂
        change flag₂=(if 2*(2:ℤ)^P<N then 1 else 0) at hflag₂
        wram_step
        · have hflagpos : flag₂≠0 := by simpa [startState] using hcond
          have hlarge : 2*(2:ℤ)^P<N := by
            by_contra he
            rw [ite_eq_right he] at hflag₂
            exact hflagpos hflag₂
          have hE0 : E≠0 := by
            intro he
            rw [he,zero_add,pow_one] at hNhi
            omega
          obtain ⟨E,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hE0
          rw [range_space_step] at hbound
          obtain ⟨hlo',hhi'⟩ := log_range_half hNhi hlarge
          have hEmw : E<2^w := by omega
          refine runs_seq_call_le hrightC (vs:=[a,L,1,heap]) (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨⟨_,_,_,_,rfl,ha,hva⟩,hz,by change heap+(2*L+1)<2^w; omega⟩
          · intro v₁ mem₁ pos₂ hp₂
            rcases hp₂ with ⟨hv₁,_,_,hf₁,hz₁,hvalid₁,hvalue₁⟩
            change v₁=heap+(2*L+1) at hv₁
            change (∀ z<heap,mem₁ z=mem z) at hf₁
            change Valid mem₁ (heap+L+1) h L at hvalid₁
            change intVal mem₁ (heap+L+1) h L=N/(2:ℤ)^1 at hvalue₁
            rw [pow_one] at hvalue₁
            have hptr₁ : heap+L+1=v₁-L := by omega
            rw [hptr₁] at hvalid₁ hvalue₁
            have hvo₁ := valid_frozen hf₁ ho hvo
            have hvt₁ := valid_frozen hf₁ ht hvt
            have hvc₁ := valid_frozen hf₁ hc hvc
            have hone₁ : intVal mem₁ one h L=(2:ℤ)^P := (value_frozen hf₁ ho).trans hone
            have htwo₁ : intVal mem₁ two h L=2*(2:ℤ)^P := (value_frozen hf₁ ht).trans htwo
            have hC₁ : intVal mem₁ c h L=C := value_frozen hf₁ hc
            have hv₁w : v₁<2^w := by omega
            have hptr₁w : v₁-L<2^w := by omega
            have hrec : MeetsContract w p b
                ((rangeLogarithmContract w h).below (fun args _ => args.getD 6 0) (E+1)) := ih
            refine runs_seq_call_le hrec (vs:=[v₁-L,one,two,c,L,P,E,v₁])
              (by eval_expr <;> simp [Expr.eval,BinOp.eval,startState,hw0,hEmw]) (by wram_words) ?_ ?_
            · refine ⟨⟨⟨_,_,_,_,_,_,_,_,rfl,hP,hP10,by omega,hPw',by omega,by omega,by omega,by omega,
                hvalid₁,hvo₁,hvt₁,hvc₁,hone₁,htwo₁,?_,?_,?_,?_⟩,
                hz₁,by change v₁+rangeLogarithmSpace L P E<2^w; omega⟩,by change E<E+1; omega⟩
              · rw [hC₁]; exact hC0
              · rw [hC₁]; exact hC1
              · rw [hvalue₁]; exact hlo'
              · rw [hvalue₁]; exact hhi'
            · intro v₂ mem₂ pos₃ hp₃
              rcases hp₃ with ⟨⟨hlo₂,hhi₂,hf₂,hz₂,_⟩,hvalid₂,hvalue₂⟩
              change v₁≤v₂ at hlo₂
              change v₂≤v₁+rangeLogarithmSpace L P E at hhi₂
              change (∀ z<v₁,mem₂ z=mem₁ z) at hf₂
              change Valid mem₂ (v₂-L) h L at hvalid₂
              change intVal mem₂ (v₂-L) h L=
                rangeLogInt P (intVal mem₁ c h L) E (intVal mem₁ (v₁-L) h L) at hvalue₂
              rw [hC₁,hvalue₁] at hvalue₂
              have hvc₂ := valid_frozen hf₂ (by omega) hvc₁
              have hC₂ : intVal mem₂ c h L=C := (value_frozen hf₂ (by omega)).trans hC₁
              have hv₂w : v₂<2^w := by omega
              have hptr₂w : v₂-L<2^w := by omega
              refine runs_seq_call_le haddC (vs:=[v₂-L,c,L,0,v₂]) (by eval_expr) (by wram_words) ?_ ?_
              · exact ⟨⟨_,_,_,_,_,rfl,by omega,by omega,by omega,hvalid₂,hvc₂⟩,
                  hz₂,by change v₂+L<2^w; omega⟩
              · intro v mem₃ pos₄ hp₄
                rcases hp₄ with ⟨hv,_,_,hf₃,hz₃,hlist₃⟩
                change v=v₂+L at hv
                change (∀ z<v₂,mem₃ z=mem₂ z) at hf₃
                change ListAt mem₃ v₂ (digits h L
                  (unsignedVal mem₂ (v₂-L) h L+unsignedVal mem₂ c h L+0)) at hlist₃
                have he : rangeLogInt P C (E+1) N=rangeLogInt P C E (N/2)+C := by
                  simp only [rangeLogInt,ite_eq_right hnsmall,ite_eq_left hlarge]
                have hsumfit : Fits h L (intVal mem₂ (v₂-L) h L+intVal mem₂ c h L+(0:ℕ)) := by
                  rw [hvalue₂,hC₂]
                  simp only [Nat.cast_zero,add_zero]
                  rw [← he]
                  exact hfit
                have hvalid₃ := (addCarry_value hlist₃).1
                have hvalue₃ := addCarry_value_of_fits hlist₃ hsumfit
                rw [hvalue₂,hC₂] at hvalue₃
                simp only [Nat.cast_zero,add_zero] at hvalue₃
                rw [← he] at hvalue₃
                have hout : v-L=v₂ := by omega
                have hvw : v<2^w := by omega
                refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
                · change (heap≤v ∧ v≤heap+rangeLogarithmSpace L P (E+1) ∧
                    (∀ z<heap,mem₃ z=mem z) ∧ ZeroFrom mem₃ v ∧ True) ∧
                    Valid mem₃ (v-L) h L ∧ intVal mem₃ (v-L) h L=rangeLogInt P C (E+1) N
                  refine ⟨⟨by omega,?_,?_,hz₃,trivial⟩,?_,?_⟩
                  · rw [range_space_step]; omega
                  · intro z hz
                    exact (hf₃ z (by omega)).trans ((hf₂ z (by omega)).trans (hf₁ z hz))
                  · rw [hout]; exact hvalid₃
                  · rw [hout]; exact hvalue₃
                · simp only [rangeLogarithmContract,Contract.below,lessContract,shiftRightContract,addCarryContract,
                    heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,
                    Expr.size_const,argsSize_cons,argsSize_nil,rangeLogarithmCost,Nat.succ_eq_add_one]
                  ring_nf
                  omega
        · have hflagzero₂ : flag₂=0 := by simpa [startState] using hcond
          have hnlarge : ¬2*(2:ℤ)^P<N := by
            intro he
            rw [ite_eq_left he] at hflag₂
            omega
          have hN0 : (2:ℤ)^P≤N := by omega
          have hN1 : N≤2*(2:ℤ)^P := by omega
          refine runs_seq_call_le hnormC (vs:=[a,one,L,P,P+4,heap])
            (by eval_expr) (by wram_words) ?_ ?_
          · refine ⟨⟨_,_,_,_,_,_,rfl,hP,by omega,ha,ho,hva,hvo,hone,hN0,hN1,
              log_series_denominator_bound hP10,?_⟩,hz,?_⟩
            · omega
            · change heap+normalizedLogarithmSpace L (P+4)<2^w
              unfold rangeLogarithmSpace at hbound
              omega
          · intro v mem₁ pos₂ hp₂
            rcases hp₂ with ⟨hv,_,_,hf₁,hz₁,hvalid₁,hvalue₁⟩
            change v=heap+normalizedLogarithmSpace L (P+4) at hv
            change (∀ z<heap,mem₁ z=mem z) at hf₁
            change Valid mem₁ (heap+normalizedLogarithmSpace L (P+4)-L) h L at hvalid₁
            change intVal mem₁ (heap+normalizedLogarithmSpace L (P+4)-L) h L=
              normalizedLogInt P N (P+4) at hvalue₁
            rw [← hv] at hvalid₁ hvalue₁
            have he : rangeLogInt P C E N=normalizedLogInt P N (P+4) := by
              cases E with
              | zero => rfl
              | succ E => simp only [rangeLogInt,ite_eq_right hnsmall,ite_eq_right hnlarge]
            have hvw : v<2^w := by unfold rangeLogarithmSpace at hbound; omega
            refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
            · change (heap≤v ∧ v≤heap+rangeLogarithmSpace L P E ∧
                (∀ z<heap,mem₁ z=mem z) ∧ ZeroFrom mem₁ v ∧ True) ∧
                Valid mem₁ (v-L) h L ∧ intVal mem₁ (v-L) h L=rangeLogInt P C E N
              refine ⟨⟨by omega,?_,hf₁,hz₁,trivial⟩,hvalid₁,?_⟩
              · unfold rangeLogarithmSpace
                omega
              · rw [he]; exact hvalue₁
            · simp only [rangeLogarithmContract,lessContract,normalizedLogarithmContract,
                heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,
                Expr.size_const,argsSize_cons,argsSize_nil,rangeLogarithmCost]
              ring_nf
              omega

end MinCostFlow.Num
