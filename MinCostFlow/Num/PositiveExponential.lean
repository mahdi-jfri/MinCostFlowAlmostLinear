module

public import MinCostFlow.Num.PositiveExponentialIntegerFacts
public import MinCostFlow.Num.ExpHorner
public import MinCostFlow.Num.RoundedSquaring
public import MinCostFlow.Num.ShiftRight
import MinCostFlow.Num.LogarithmRangeFacts
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Verified exponential on nonnegative inputs

Shift the argument right by `B+2` bits, evaluate `P+4` rounded Taylor steps,
and square `B+2` times. The separate real-analysis bounds give relative error
and show that every stored result fits. All procedures use the shared heap.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Fresh cells used by the positive exponential. -/
def positiveExponentialSpace (L P B : ℕ) : ℕ :=
  (2*L+1)+expHornerSpace L (P+4)+roundedSquaringSpace L (B+2)

/-- Explicit polynomial cost of the positive exponential. -/
def positiveExponentialCost (L P B : ℕ) : ℕ :=
  (P+4)*(500*L^2+2000*L+2000)+(B+2)*(200*L^2+500*L+500)+100*L+1000

/-- Arguments `[x,one,L,P,B,heap]`. -/
def positiveExponentialBody (shift horner square : ℕ) : Stmt :=
  .call 6 shift [.reg 0,.reg 2,.bin .add (.reg 4) (.const 2),.reg 5] ;;
  .call 7 horner [.bin .sub (.reg 6) (.reg 2),.reg 1,.reg 2,.reg 3,
    .const 0,.bin .add (.reg 3) (.const 4),.reg 6] ;;
  .call 8 square [.bin .sub (.reg 7) (.reg 2),.reg 2,.reg 3,.reg 4,
    .bin .add (.reg 4) (.const 2),.reg 7] ;;
  .ret (.reg 8)

/-- The positive exponential entry and all its arithmetic procedures. -/
def positiveExponentialModule (b h : ℕ) : List Stmt :=
  [positiveExponentialBody (b+1) (b+5) (b+45)] ++
    (shiftRightModule (b+1) h ++ (expHornerModule (b+5) h ++ roundedSquaringModule (b+45) h))

/-- Relative exponential error on `0≤x≤B`. The output is at least one and
never exceeds the true exponential. The reusable constant `one` has numerator
`2^P`. Precision `q+B+10` and width `P+2B+4` suffice. -/
def positiveExponentialContract (w h q : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a one L P B heap,args=[a,one,L,P,B,heap] ∧ h∣P ∧
      q+B+10≤P ∧ P+2*B+4≤h*L ∧ 2*P+9<2^w ∧ a+L≤heap ∧ one+L≤heap ∧
      Valid mem a h L ∧ Valid mem one h L ∧ intVal mem one h L=(2:ℤ)^P ∧
      0 ≤ intVal mem a h L ∧ fixVal mem a h L P≤B)
    (fun args mem mem' =>
      let out := heapArg args+positiveExponentialSpace (args.getD 2 0) (args.getD 3 0) (args.getD 4 0)-args.getD 2 0
      Valid mem' out h (args.getD 2 0) ∧
      1≤fixVal mem' out h (args.getD 2 0) (args.getD 3 0) ∧
      fixVal mem' out h (args.getD 2 0) (args.getD 3 0)≤
        Real.exp (fixVal mem (args.getD 0 0) h (args.getD 2 0) (args.getD 3 0)) ∧
      |fixVal mem' out h (args.getD 2 0) (args.getD 3 0)-
        Real.exp (fixVal mem (args.getD 0 0) h (args.getD 2 0) (args.getD 3 0))|≤
        (1/(2:ℝ)^q)*Real.exp (fixVal mem (args.getD 0 0) h (args.getD 2 0) (args.getD 3 0)))
    (fun args _ => positiveExponentialCost (args.getD 2 0) (args.getD 3 0) (args.getD 4 0))
    (fun args _ => positiveExponentialSpace (args.getD 2 0) (args.getD 3 0) (args.getD 4 0))
  { C with post := fun args mem v mem' =>
    v=heapArg args+positiveExponentialSpace (args.getD 2 0) (args.getD 3 0) (args.getD 4 0) ∧ C.post args mem v mem' }

/-- The positive exponential module uses no randomness. -/
theorem positiveExponentialModule_noRand (b h : ℕ) : ∀ s∈positiveExponentialModule b h,s.NoRand := by
  intro s hs
  simp only [positiveExponentialModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hs | hh | hsq
  · simp [positiveExponentialBody,Stmt.NoRand]
  · exact shiftRightModule_noRand _ _ _ hs
  · exact expHornerModule_noRand _ _ _ hh
  · exact roundedSquaringModule_noRand _ _ _ hsq

/-- Positive exponential evaluation meets its real relative-error contract.
The exact power bound needed by squaring follows from the Taylor underestimate. -/
theorem positiveExponential_meetsContract {w h b q : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (positiveExponentialModule b h)) :
    MeetsContract w p b (positiveExponentialContract w h q) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hs := hasAt_append_left ht
  have ht₂ := hasAt_append_right ht
  change p.HasAt (b+5) _ at ht₂
  have hhplace := hasAt_append_left ht₂
  have hsq := hasAt_append_right ht₂
  change p.HasAt (b+45) _ at hsq
  have hb := base_lt_word (show 2*h+2≤w by omega)
  have hw1 : 1<2^w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  have hsC := shiftRight_meetsContract hh hw1 hb hs
  have hhC := expHorner_meetsContract hh hw hhplace
  have hsqC := roundedSquaring_meetsContract hh (show 2*h+2≤w by omega) hsq
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a,one,L,P,B,heap,rfl,hP,hprec,hwidth,hPw',ha,ho,hva,hvo,hone,hN0,hNB⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+positiveExponentialSpace L P B<2^w at hbound
  unfold positiveExponentialSpace at hbound
  have hP10 : 10≤P := by omega
  have hHspace : L≤expHornerSpace L (P+4) := by unfold expHornerSpace; omega
  have hSqspace : L≤roundedSquaringSpace L (B+2) := by unfold roundedSquaringSpace; omega
  have haw : a<2^w := hwords a (by simp)
  have how : one<2^w := hwords one (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPw : P<2^w := hwords P (by simp)
  have hBw : B<2^w := hwords B (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have hP4w : P+4<2^w := by omega
  have hB2w : B+2<2^w := by omega
  obtain ⟨hY0,hY1⟩ := positiveExp_reduced_bounds hN0 hNB
  have hpow := positiveExp_horner_power_bound hN0 hNB
  apply runs_start_le
  unfold positiveExponentialBody
  refine runs_seq_call_le hsC (vs:=[a,L,B+2,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,rfl,ha,hva⟩,hz,by change heap+(2*L+1)<2^w; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨hv₁,_,_,hf₁,hz₁,hvalid₁,hvalue₁⟩
    change v₁=heap+(2*L+1) at hv₁
    change (∀ z<heap,mem₁ z=mem z) at hf₁
    change Valid mem₁ (heap+L+1) h L at hvalid₁
    change intVal mem₁ (heap+L+1) h L=intVal mem a h L/(2:ℤ)^(B+2) at hvalue₁
    have hptr₁ : heap+L+1=v₁-L := by omega
    rw [hptr₁] at hvalid₁ hvalue₁
    have hvo₁ : Valid mem₁ one h L := by
      intro i hi
      rw [hf₁ _ (by omega)]
      exact hvo i hi
    have hone₁ : intVal mem₁ one h L=(2:ℤ)^P :=
      (intVal_congr (fun i hi => hf₁ _ (by omega))).trans hone
    have hv₁w : v₁<2^w := by omega
    have hptr₁w : v₁-L<2^w := by omega
    refine runs_seq_call_le hhC (vs:=[v₁-L,one,L,P,0,P+4,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · refine ⟨⟨_,_,_,_,_,_,_,rfl,hP,by omega,by omega,by omega,hvalid₁,hvo₁,hone₁,?_,?_,?_,?_⟩,
        hz₁,by change v₁+expHornerSpace L (P+4)<2^w; omega⟩
      · rw [hvalue₁]; exact hY0
      · rw [hvalue₁]; exact hY1
      · have hd := log_series_denominator_bound hP10
        omega
      · omega
    · intro v₂ mem₂ pos₂ hp₂
      rcases hp₂ with ⟨hv₂,_,_,hf₂,hz₂,hvalid₂,hvalue₂⟩
      change v₂=v₁+expHornerSpace L (P+4) at hv₂
      change (∀ z<v₁,mem₂ z=mem₁ z) at hf₂
      change Valid mem₂ (v₁+expHornerSpace L (P+4)-L) h L at hvalid₂
      change intVal mem₂ (v₁+expHornerSpace L (P+4)-L) h L=
        expHornerInt P (intVal mem₁ (v₁-L) h L) 0 (P+4) at hvalue₂
      rw [← hv₂,hvalue₁] at hvalue₂
      rw [← hv₂] at hvalid₂
      obtain ⟨hA0,_⟩ := expHornerInt_bounds hY0 hY1 0 (P+4)
      have hv₂w : v₂<2^w := by omega
      have hptr₂w : v₂-L<2^w := by omega
      refine runs_seq_call_le hsqC (vs:=[v₂-L,L,P,B,B+2,v₂]) (by eval_expr) (by wram_words) ?_ ?_
      · refine ⟨⟨_,_,_,_,_,_,rfl,hP,hwidth,by omega,hvalid₂,?_,?_⟩,
          hz₂,by change v₂+roundedSquaringSpace L (B+2)<2^w; omega⟩
        · rw [hvalue₂]; exact hA0
        · change ((intVal mem₂ (v₂-L) h L:ℝ)/(2:ℝ)^P)^(2^(B+2))≤_
          rw [hvalue₂]; exact hpow
      · intro v mem₃ pos₃ hp₃
        rcases hp₃ with ⟨hv,_,_,hf₃,hz₃,hvalid₃,hvalue₃⟩
        change v=v₂+roundedSquaringSpace L (B+2) at hv
        change (∀ z<v₂,mem₃ z=mem₂ z) at hf₃
        change Valid mem₃ (v₂+roundedSquaringSpace L (B+2)-L) h L at hvalid₃
        change intVal mem₃ (v₂+roundedSquaringSpace L (B+2)-L) h L=
          squaresInt P (intVal mem₂ (v₂-L) h L) (B+2) at hvalue₃
        rw [hvalue₂] at hvalue₃
        have he : v=heap+positiveExponentialSpace L P B := by unfold positiveExponentialSpace; omega
        have hout : heap+positiveExponentialSpace L P B-L=v₂+roundedSquaringSpace L (B+2)-L := by
          unfold positiveExponentialSpace; omega
        have hvalue : fixVal mem₃ (heap+positiveExponentialSpace L P B-L) h L P=
            positiveExpRounded P B (fixVal mem a h L P) := by
          rw [hout,fixVal,hvalue₃]
          exact positiveExpInt_value P B (intVal mem a h L)
        have hx0 : 0≤fixVal mem a h L P := div_nonneg (by exact_mod_cast hN0) (by positivity)
        obtain ⟨hlo,hhi⟩ := positiveExpRounded_bounds hx0 hNB P
        have herr := positiveExpRounded_relative hx0 hNB (show q+B+5≤P by omega)
        have hvw : v<2^w := by omega
        refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
        · change v=heap+positiveExponentialSpace L P B ∧ heap≤v ∧ v≤heap+positiveExponentialSpace L P B ∧
            (∀ z<heap,mem₃ z=mem z) ∧ ZeroFrom mem₃ v ∧
            Valid mem₃ (heap+positiveExponentialSpace L P B-L) h L ∧
            1≤fixVal mem₃ (heap+positiveExponentialSpace L P B-L) h L P ∧
            fixVal mem₃ (heap+positiveExponentialSpace L P B-L) h L P≤Real.exp (fixVal mem a h L P) ∧
            |fixVal mem₃ (heap+positiveExponentialSpace L P B-L) h L P-Real.exp (fixVal mem a h L P)|≤
              (1/(2:ℝ)^q)*Real.exp (fixVal mem a h L P)
          refine ⟨he,by omega,by omega,?_,hz₃,?_,?_,?_,?_⟩
          · intro z hz
            exact (hf₃ z (by omega)).trans ((hf₂ z (by omega)).trans (hf₁ z hz))
          · rw [hout]; exact hvalid₃
          · rw [hvalue]; exact hlo
          · rw [hvalue]; exact hhi
          · rw [hvalue]; exact herr
        · simp only [positiveExponentialContract,shiftRightContract,expHornerContract,roundedSquaringContract,
            heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,
            Expr.size_const,argsSize_cons,argsSize_nil,positiveExponentialCost]
          ring_nf
          omega

end MinCostFlow.Num
