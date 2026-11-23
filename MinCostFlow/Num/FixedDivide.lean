module

public import MinCostFlow.Num.SignExtend
public import MinCostFlow.Num.ShiftLeft
public import MinCostFlow.Num.IntegerDivide
public import MinCostFlow.Num.Copy
import MinCostFlow.Num.FixedDivideFacts
import MinCostFlow.Num.ShiftFacts
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Fixed-point division

Extend both operands to three times their width, shift the numerator by the precision,
and use signed floor division. A fitting output bounds the shifted numerator, so the
shift is exact. Copying the low output limbs gives the exact fixed-point quotient.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Fresh cells used by fixed-point division, including the final `L`-limb output. -/
def fixedDivideSpace (L : ℕ) : ℕ := 10*L+integerDivideSpace (3*L)

/-- Arguments `[a,d,L,P,heap]`. -/
def fixedDivideBody (extend shift divide copy : ℕ) : Stmt :=
  .call 5 extend [.reg 0,.reg 2,.bin .mul (.const 3) (.reg 2),.reg 4] ;;
  .call 6 extend [.reg 1,.reg 2,.bin .mul (.const 3) (.reg 2),.reg 5] ;;
  .call 7 shift [.reg 4,.bin .mul (.const 3) (.reg 2),.reg 3,.reg 6] ;;
  .call 8 divide [.reg 6,.reg 5,.bin .mul (.const 3) (.reg 2),.reg 7] ;;
  .call 9 copy [.bin .sub (.reg 8) (.bin .mul (.const 3) (.reg 2)),.reg 2,.reg 8] ;;
  .ret (.reg 9)

/-- Fixed division and all of its verified dependencies. -/
def fixedDivideModule (b h : ℕ) : List Stmt :=
  [fixedDivideBody (b+1) (b+4) (b+6) (b+31)] ++
    (signExtendModule (b+1) h ++ (shiftLeftModule (b+4) h ++
      (integerDivideModule (b+6) h ++ copyModule (b+31))))

/-- Exact fixed-point division, with a fitting-result precondition. Precision is a
multiple of the limb width. A zero divisor is excluded. -/
def fixedDivideContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a d L P heap,args=[a,d,L,P,heap] ∧ h∣P ∧ a+L≤heap ∧ d+L≤heap ∧
      Valid mem a h L ∧ Valid mem d h L ∧ intVal mem d h L≠0 ∧
      Fits h L (floorDiv (intVal mem a h L*(2:ℤ)^P) (intVal mem d h L)))
    (fun args mem mem' =>
      Valid mem' (heapArg args+9*args.getD 2 0+integerDivideSpace (3*args.getD 2 0)) h (args.getD 2 0) ∧
      intVal mem' (heapArg args+9*args.getD 2 0+integerDivideSpace (3*args.getD 2 0)) h (args.getD 2 0)=
        floorDiv (intVal mem (args.getD 0 0) h (args.getD 2 0)*(2:ℤ)^args.getD 3 0)
          (intVal mem (args.getD 1 0) h (args.getD 2 0)))
    (fun args _ => (3*args.getD 2 0)*(900*args.getD 2 0+644)+900*args.getD 2 0+700)
    (fun args _ => fixedDivideSpace (args.getD 2 0))
  { C with post := fun args mem v mem' => v=heapArg args+fixedDivideSpace (args.getD 2 0) ∧ C.post args mem v mem' }

/-- Fixed-point division uses no random statement. -/
theorem fixedDivideModule_noRand (b h : ℕ) : ∀ s∈fixedDivideModule b h,s.NoRand := by
  intro s hs
  simp only [fixedDivideModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | he | hs | hd | hc
  · simp [fixedDivideBody,Stmt.NoRand]
  · exact signExtendModule_noRand _ _ _ he
  · exact shiftLeftModule_noRand _ _ _ hs
  · exact integerDivideModule_noRand _ _ _ hd
  · have he : s=copyBody := by simpa [copyModule] using hc
    subst s; exact copyBody_noRand

/-- Fixed-point floor division meets its heap contract with quadratic cost. -/
theorem fixedDivide_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (fixedDivideModule b h)) :
    MeetsContract w p b (fixedDivideContract w h) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have he := hasAt_append_left ht
  have ht₂ := hasAt_append_right ht
  change p.HasAt (b+4) _ at ht₂
  have hs := hasAt_append_left ht₂
  have ht₃ := hasAt_append_right ht₂
  change p.HasAt (b+6) _ at ht₃
  have hd := hasAt_append_left ht₃
  have hc := hasAt_append_right ht₃
  change p.HasAt (b+31) _ at hc
  have hb := base_lt_word (show 2*h+2≤w by omega)
  have hw1 : 1<2^w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  have hw3 : 3<2^w := lt_of_lt_of_le (by decide : 3<2^3)
    (Nat.pow_le_pow_right (by decide) (show 3≤w by omega))
  have heC := signExtend_meetsContract hh hw1 hb he
  have hsC := shiftLeft_meetsContract hh (show 2*h+2≤w by omega) hs
  have hdC := integerDivide_meetsContract hh hw hd
  have hcC := copy_meetsContract (h:=h) hw1 hc
  have hentry : p.procs[b]?=some (fixedDivideBody (b+1) (b+4) (b+6) (b+31)) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a,d,L,P,heap,rfl,hP,ha,hd,hva,hvd,hne,hfit⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+fixedDivideSpace L<2^w at hbound
  have hbound' : heap+10*L+integerDivideSpace (3*L)<2^w := by
    simpa only [fixedDivideSpace,Nat.add_assoc] using hbound
  have hspace : 9*L+2 ≤ integerDivideSpace (3*L) := by unfold integerDivideSpace unsignedDivideSpace; omega
  have haw : a<2^w := hwords a (by simp)
  have hdw : d<2^w := hwords d (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPw : P<2^w := hwords P (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have h3Lw : 3*L<2^w := by omega
  have hscaled := fits_numerator_of_floorDiv_fits hh hne (intVal_natAbs_lt hvd) hfit
  apply runs_start_le
  unfold fixedDivideBody
  refine runs_seq_call_le heC (vs:=[a,L,3*L,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨a,L,3*L,heap,rfl,by omega,ha,hva⟩,hz,by change heap+3*L<2^w; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨hv₁,hlo₁,hhi₁,hf₁,hz₁,hvalid₁,hvalue₁⟩
    change v₁=heap+3*L at hv₁
    change (∀ z<heap,mem₁ z=mem z) at hf₁
    change Valid mem₁ heap h (3*L) at hvalid₁
    change intVal mem₁ heap h (3*L)=intVal mem a h L at hvalue₁
    have hvd₁ : Valid mem₁ d h L := by intro i hi; rw [hf₁ _ (by omega)]; exact hvd i hi
    have hde : intVal mem₁ d h L=intVal mem d h L := intVal_congr (fun i hi => hf₁ _ (by omega))
    have hv₁w : v₁<2^w := by omega
    refine runs_seq_call_le heC (vs:=[d,L,3*L,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨d,L,3*L,v₁,rfl,by omega,by omega,hvd₁⟩,hz₁,by change v₁+3*L<2^w; omega⟩
    · intro v₂ mem₂ pos₂ hp₂
      rcases hp₂ with ⟨hv₂,hlo₂,hhi₂,hf₂,hz₂,hvalid₂,hvalue₂⟩
      change v₂=v₁+3*L at hv₂
      change (∀ z<v₁,mem₂ z=mem₁ z) at hf₂
      change Valid mem₂ v₁ h (3*L) at hvalid₂
      change intVal mem₂ v₁ h (3*L)=intVal mem₁ d h L at hvalue₂
      rw [hde] at hvalue₂
      have hva₂ : Valid mem₂ heap h (3*L) := by intro i hi; rw [hf₂ _ (by omega)]; exact hvalid₁ i hi
      have hvalueA : intVal mem₂ heap h (3*L)=intVal mem a h L :=
        (intVal_congr (fun i hi => hf₂ _ (by omega))).trans hvalue₁
      have hv₂w : v₂<2^w := by omega
      refine runs_seq_call_le hsC (vs:=[heap,3*L,P,v₂]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨heap,3*L,P,v₂,rfl,by omega,hva₂⟩,hz₂,by change v₂+3*L<2^w; omega⟩
      · intro v₃ mem₃ pos₃ hp₃
        rcases hp₃ with ⟨hv₃,hlo₃,hhi₃,hf₃,hz₃,hvalid₃,hvalue₃⟩
        change v₃=v₂+3*L at hv₃
        change (∀ z<v₂,mem₃ z=mem₂ z) at hf₃
        change Valid mem₃ v₂ h (3*L) at hvalid₃
        change intVal mem₃ v₂ h (3*L)=wrap h (3*L) (intVal mem₂ heap h (3*L)*(2:ℤ)^P) at hvalue₃
        rw [hvalueA,wrap_of_fits hscaled] at hvalue₃
        have hvd₃ : Valid mem₃ v₁ h (3*L) := by intro i hi; rw [hf₃ _ (by omega)]; exact hvalid₂ i hi
        have hdval : intVal mem₃ v₁ h (3*L)=intVal mem d h L :=
          (intVal_congr (fun i hi => hf₃ _ (by omega))).trans hvalue₂
        have hv₃w : v₃<2^w := by omega
        refine runs_seq_call_le hdC (vs:=[v₂,v₁,3*L,v₃]) (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨⟨v₂,v₁,3*L,v₃,rfl,by omega,by omega,hvalid₃,hvd₃,by rw [hdval]; exact hne⟩,
            hz₃,by change v₃+integerDivideSpace (3*L)<2^w; omega⟩
        · intro v₄ mem₄ pos₄ hp₄
          rcases hp₄ with ⟨hv₄,hlo₄,hhi₄,hf₄,hz₄,hvalid₄,hvalue₄⟩
          change v₄=v₃+integerDivideSpace (3*L) at hv₄
          change (∀ z<v₃,mem₄ z=mem₃ z) at hf₄
          change Valid mem₄ (v₃+2*(3*L)+unsignedDivideSpace (3*L)) h (3*L) at hvalid₄
          change intVal mem₄ (v₃+2*(3*L)+unsignedDivideSpace (3*L)) h (3*L)=
            wrap h (3*L) (floorDiv (intVal mem₃ v₂ h (3*L)) (intVal mem₃ v₁ h (3*L))) at hvalue₄
          rw [hvalue₃,hdval,wrap_of_fits (fits_of_length_le (show L≤3*L by omega) hfit)] at hvalue₄
          have hout : v₄-3*L=v₃+2*(3*L)+unsignedDivideSpace (3*L) := by
            unfold integerDivideSpace at hv₄; omega
          have hprefix : Valid mem₄ (v₄-3*L) h L := by
            rw [hout]; exact fun i hi => hvalid₄ i (by omega)
          have hpvalue : intVal mem₄ (v₄-3*L) h L=
              floorDiv (intVal mem a h L*(2:ℤ)^P) (intVal mem d h L) := by
            rw [hout,intVal_prefix_wrap hvalid₄ (show L≤3*L by omega),hvalue₄,wrap_of_fits hfit]
          have hv₄w : v₄<2^w := by omega
          have hptrw : v₄-3*L<2^w := by omega
          refine runs_seq_call_le hcC (vs:=[v₄-3*L,L,v₄]) (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨⟨v₄-3*L,L,v₄,rfl,by omega,hprefix⟩,hz₄,by change v₄+L<2^w; omega⟩
          · intro v mem₅ pos₅ hp₅
            rcases hp₅ with ⟨hv,hlo,hhi,hf₅,hz₅,hlimbs,hvalid,hvalue⟩
            change v=v₄+L at hv
            change (∀ z<v₄,mem₅ z=mem₄ z) at hf₅
            change Valid mem₅ v₄ h L at hvalid
            change intVal mem₅ v₄ h L=intVal mem₄ (v₄-3*L) h L at hvalue
            rw [hpvalue] at hvalue
            have hvw : v<2^w := by omega
            refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
            · change v=heap+fixedDivideSpace L ∧ heap≤v ∧ v≤heap+fixedDivideSpace L ∧
                (∀ z<heap,mem₅ z=mem z) ∧ ZeroFrom mem₅ v ∧
                Valid mem₅ (heap+9*L+integerDivideSpace (3*L)) h L ∧
                intVal mem₅ (heap+9*L+integerDivideSpace (3*L)) h L=
                  floorDiv (intVal mem a h L*(2:ℤ)^P) (intVal mem d h L)
              have he : v₄=heap+9*L+integerDivideSpace (3*L) := by omega
              have hvexact : v=heap+fixedDivideSpace L := by unfold fixedDivideSpace; omega
              refine ⟨hvexact,by omega,by omega,?_,hz₅,?_,?_⟩
              · intro z hz
                exact (hf₅ z (by omega)).trans ((hf₄ z (by omega)).trans ((hf₃ z (by omega)).trans
                  ((hf₂ z (by omega)).trans (hf₁ z hz))))
              · simpa only [he] using hvalid
              · simpa only [he] using hvalue
            · simp only [fixedDivideContract,signExtendContract,shiftLeftContract,integerDivideContract,
                copyContract,heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,
                Expr.size_bin,Expr.size_const,argsSize_cons,argsSize_nil,
                show 300*(3*L)=900*L by omega]
              omega

end MinCostFlow.Num
