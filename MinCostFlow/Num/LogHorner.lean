module

public import MinCostFlow.Num.LogHornerIntegerFacts
public import MinCostFlow.Num.LoadSmall
public import MinCostFlow.Num.IntegerDivide
public import MinCostFlow.Num.FixedMultiply
public import MinCostFlow.Num.AddCarry
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Fixed-point Horner evaluation for the logarithm

Evaluate the last coefficient first. Each step loads its odd denominator,
divides the stored one by it, multiplies the tail by the stored square, and
adds the two results. All results use the same precision and limb count.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Fresh cells for one Horner step. -/
def logHornerStepSpace (L : ℕ) : ℕ := 13*L+integerDivideSpace L+1

/-- Space for all terms and the initial zero tail. -/
def logHornerSpace (L n : ℕ) : ℕ := n*logHornerStepSpace L+L

/-- Arguments `[square,one,L,P,i,n,heap]`. -/
def logHornerBody (self load divide mul add : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 5) (.const 0))
    (.ret (.bin .add (.reg 6) (.reg 2)))
    (.call 7 self [.reg 0,.reg 1,.reg 2,.reg 3,.bin .add (.reg 4) (.const 1),
        .bin .sub (.reg 5) (.const 1),.reg 6] ;;
     .call 8 load [.bin .add (.bin .mul (.const 2) (.reg 4)) (.const 1),.reg 2,.reg 7] ;;
     .call 9 divide [.reg 1,.reg 7,.reg 2,.reg 8] ;;
     .call 10 mul [.reg 0,.bin .sub (.reg 7) (.reg 2),.reg 2,.reg 3,.reg 9] ;;
     .call 11 add [.bin .sub (.reg 9) (.reg 2),.bin .sub (.reg 10) (.reg 2),
        .reg 2,.const 0,.reg 10] ;;
     .ret (.reg 11))

/-- Horner evaluation and its closed arithmetic dependencies. -/
def logHornerModule (b h : ℕ) : List Stmt :=
  [logHornerBody b (b+1) (b+2) (b+27) (b+38)] ++
    (loadSmallModule (b+1) h ++ (integerDivideModule (b+2) h ++
      (fixedMultiplyModule (b+27) h ++ addCarryModule (b+38) h)))

/-- Exact rounded Horner evaluation. Four spare bits ensure that none of the
intermediate arithmetic wraps. -/
def logHornerContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ s one L P i n heap,args=[s,one,L,P,i,n,heap] ∧
      h∣P ∧ P+4≤h*L ∧ s+L≤heap ∧ one+L≤heap ∧
      Valid mem s h L ∧ Valid mem one h L ∧ intVal mem one h L=(2:ℤ)^P ∧
      0 ≤ intVal mem s h L ∧ 2*intVal mem s h L≤(2:ℤ)^P ∧
      2*(i+n)+1≤2^P ∧ 2*(i+n)+1<2^w)
    (fun args mem mem' =>
      Valid mem' (heapArg args+logHornerSpace (args.getD 2 0) (args.getD 5 0)-args.getD 2 0)
        h (args.getD 2 0) ∧
      intVal mem' (heapArg args+logHornerSpace (args.getD 2 0) (args.getD 5 0)-args.getD 2 0)
        h (args.getD 2 0)=logHornerInt (args.getD 3 0)
          (intVal mem (args.getD 0 0) h (args.getD 2 0)) (args.getD 4 0) (args.getD 5 0))
    (fun args _ => args.getD 5 0*(500*(args.getD 2 0)^2+2000*args.getD 2 0+2000)+10)
    (fun args _ => logHornerSpace (args.getD 2 0) (args.getD 5 0))
  { C with post := fun args mem v mem' =>
    v=heapArg args+logHornerSpace (args.getD 2 0) (args.getD 5 0) ∧ C.post args mem v mem' }

/-- Every body of the Horner module is deterministic. -/
theorem logHornerModule_noRand (b h : ℕ) : ∀ s∈logHornerModule b h,s.NoRand := by
  intro s hs
  simp only [logHornerModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hl | hd | hm | ha
  · simp [logHornerBody,Stmt.NoRand]
  · have he : s=loadSmallBody (b+1) h := by simpa [loadSmallModule] using hl
    subst s
    exact loadSmallBody_noRand _ _
  · exact integerDivideModule_noRand _ _ _ hd
  · exact fixedMultiplyModule_noRand _ _ _ hm
  · have he : s=addCarryBody (b+38) h := by simpa [addCarryModule] using ha
    subst s
    exact addCarryBody_noRand _ _

private theorem valid_frozen {mem mem' : ℕ→ℕ} {a h L heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) (hv : Valid mem a h L) :
    Valid mem' a h L := by
  intro i hi
  rw [hf _ (by omega)]
  exact hv i hi

private theorem value_frozen {mem mem' : ℕ→ℕ} {a h L heap : ℕ}
    (hf : ∀ z<heap,mem' z=mem z) (ha : a+L≤heap) :
    intVal mem' a h L=intVal mem a h L := intVal_congr (fun i hi => hf _ (by omega))

private theorem loadSmall_decode {mem : ℕ→ℕ} {h L n a : ℕ}
    (hl : ListAt mem a (digits h L n)) (hf : Fits h L (n:ℤ)) :
    intVal mem a h L=(n:ℤ) := by
  rw [(loadSmall_value hl).2.2]
  have he : residue h L (n:ℤ)=n%capacity h L := by
    simp only [residue,← Int.natCast_mod,Int.toNat_natCast]
  rw [← he]
  exact wrap_of_fits hf

private theorem horner_space_step (L n : ℕ) :
    logHornerSpace L (n+1)=logHornerSpace L n+L+integerDivideSpace L+(11*L+1)+L := by
  unfold logHornerSpace logHornerStepSpace
  ring

/-- Horner evaluation meets its heap contract, with quadratic cost per term.
The range lemmas ensure that division, multiplication, and addition are exact
at their specified rounded numerators. -/
theorem logHorner_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (logHornerModule b h)) :
    MeetsContract w p b (logHornerContract w h) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hl := hasAt_append_left ht
  have ht₂ := hasAt_append_right ht
  change p.HasAt (b+2) _ at ht₂
  have hd := hasAt_append_left ht₂
  have ht₃ := hasAt_append_right ht₂
  change p.HasAt (b+27) _ at ht₃
  have hm := hasAt_append_left ht₃
  have ha := hasAt_append_right ht₃
  change p.HasAt (b+38) _ at ha
  have hb := base_lt_word (show 2*h+2≤w by omega)
  have hw1 : 1<2^w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  have hw0 : w≠0 := by omega
  have hw2 : 2<2^w := lt_of_lt_of_le (by decide : 2<2^2)
    (Nat.pow_le_pow_right (by decide) (show 2≤w by omega))
  have hlC := loadSmall_meetsContract hw1 hb hl
  have hdC := integerDivide_meetsContract hh hw hd
  have hmC := fixedMultiply_meetsContract hh (show 2*h+2≤w by omega) hm
  have haC := addCarry_meetsContract hh (show 2*h+2≤w by omega) ha
  apply meetsContract_of_rec (fun args _ => args.getD 5 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨⟨s,one,L,P,i,n,heap,rfl,hP,hwidth,hs,ho,hvs,hvo,hone,hs0,hs2,hden,hdenw⟩,hz,hbound⟩
  change n=k at hk
  subst k
  change ZeroFrom mem heap at hz
  change heap+logHornerSpace L n<2^w at hbound
  have hsw : s<2^w := hwords s (by simp)
  have how : one<2^w := hwords one (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPw : P<2^w := hwords P (by simp)
  have hiw : i<2^w := hwords i (by simp)
  have hnw : n<2^w := hwords n (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  apply runs_start_le
  unfold logHornerBody
  wram_step
  · have hn0 : n=0 := by simpa [startState] using hcond
    subst n
    have hend : heap+L<2^w := by simpa [logHornerSpace] using hbound
    refine runs_ret_le (v:=heap+L) (by eval_expr) ?_ ?_
    · change heap+L=heap+logHornerSpace L 0 ∧ heap≤heap+L ∧
        heap+L≤heap+logHornerSpace L 0 ∧ (∀ z<heap,mem z=mem z) ∧
        ZeroFrom mem (heap+L) ∧
        Valid mem (heap+logHornerSpace L 0-L) h L ∧
        intVal mem (heap+logHornerSpace L 0-L) h L=logHornerInt P (intVal mem s h L) i 0
      simp only [logHornerSpace,zero_mul,zero_add,Nat.add_sub_cancel,logHornerInt]
      exact ⟨trivial,by omega,le_rfl,fun _ _ => trivial,hz.mono (by omega),
        zeroFrom_valid hz le_rfl,intVal_zeroFrom hz le_rfl⟩
    · simp only [logHornerContract,heapContract,List.getD_cons_zero,List.getD_cons_succ,
        Expr.size_reg,Expr.size_bin,Expr.size_const]
      omega
  · have hn0 : n≠0 := by simpa [startState] using hcond
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hipw : i+1<2^w := by omega
    have hoddw : 2*i+1<2^w := by omega
    have h2iw : 2*i<2^w := by omega
    have hn' : n<2^w := by omega
    rw [horner_space_step] at hbound
    have hrec : MeetsContract w p b
        ((logHornerContract w h).below (fun args _ => args.getD 5 0) (n+1)) := ih
    refine runs_seq_call_le hrec (vs:=[s,one,L,P,i+1,n,heap])
      (by eval_expr <;> simp [Expr.eval,BinOp.eval,startState,hw0,hn']) (by wram_words) ?_ ?_
    · refine ⟨⟨⟨s,one,L,P,i+1,n,heap,rfl,hP,hwidth,hs,ho,hvs,hvo,hone,hs0,hs2,?_,?_⟩,
        hz,by change heap+logHornerSpace L n<2^w; omega⟩,by change n<n+1; omega⟩
      · convert hden using 1 <;> omega
      · convert hdenw using 1 <;> omega
    · intro v₁ mem₁ pos₁ hp₁
      rcases hp₁ with ⟨hv₁,_,_,hf₁,hz₁,hvalid₁,hvalue₁⟩
      change v₁=heap+logHornerSpace L n at hv₁
      change (∀ z<heap,mem₁ z=mem z) at hf₁
      change Valid mem₁ (heap+logHornerSpace L n-L) h L at hvalid₁
      change intVal mem₁ (heap+logHornerSpace L n-L) h L=
        logHornerInt P (intVal mem s h L) (i+1) n at hvalue₁
      rw [← hv₁] at hvalid₁ hvalue₁
      have hlow : L≤v₁ := by rw [hv₁]; unfold logHornerSpace; omega
      have hv₁w : v₁<2^w := by omega
      have hptr₁w : v₁-L<2^w := by omega
      refine runs_seq_call_le hlC (vs:=[2*i+1,L,v₁]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨_,_,_,rfl⟩,hz₁,by change v₁+L<2^w; omega⟩
      · intro v₂ mem₂ pos₂ hp₂
        rcases hp₂ with ⟨hv₂,_,_,hf₂,hz₂,hlist₂⟩
        change v₂=v₁+L at hv₂
        change (∀ z<v₁,mem₂ z=mem₁ z) at hf₂
        change ListAt mem₂ v₁ (digits h L (2*i+1)) at hlist₂
        have hd0 : (0:ℤ)<(2*i+1:ℕ) := by omega
        have hdcap : (2*i+1:ℕ)≤(2:ℤ)^P := by
          have hh : 2*i+1≤2^P := le_trans (by omega) hden
          exact_mod_cast hh
        have hdfit : Fits h L (2*i+1:ℕ) := fits_twice_scale hwidth (by omega) (by omega)
        have hvalidD := (loadSmall_value hlist₂).1
        have hvalueD := loadSmall_decode hlist₂ hdfit
        have hone₂ : intVal mem₂ one h L=(2:ℤ)^P :=
          (value_frozen hf₂ (by omega)).trans ((value_frozen hf₁ ho).trans hone)
        have hvo₂ : Valid mem₂ one h L :=
          valid_frozen hf₂ (by omega) (valid_frozen hf₁ ho hvo)
        have hv₂w : v₂<2^w := by omega
        refine runs_seq_call_le hdC (vs:=[one,v₁,L,v₂]) (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨⟨_,_,_,_,rfl,by omega,by omega,hvo₂,hvalidD,by rw [hvalueD]; omega⟩,
            hz₂,by change v₂+integerDivideSpace L<2^w; omega⟩
        · intro v₃ mem₃ pos₃ hp₃
          rcases hp₃ with ⟨hv₃,_,_,hf₃,hz₃,hvalid₃,hvalue₃⟩
          change v₃=v₂+integerDivideSpace L at hv₃
          change (∀ z<v₂,mem₃ z=mem₂ z) at hf₃
          change Valid mem₃ (v₂+2*L+unsignedDivideSpace L) h L at hvalid₃
          change intVal mem₃ (v₂+2*L+unsignedDivideSpace L) h L=
            wrap h L (floorDiv (intVal mem₂ one h L) (intVal mem₂ v₁ h L)) at hvalue₃
          have hptr₃ : v₂+2*L+unsignedDivideSpace L=v₃-L := by
            unfold integerDivideSpace at hv₃; omega
          rw [hptr₃] at hvalid₃ hvalue₃
          obtain ⟨hc0,hc1⟩ := logHornerInt_coefficient_bounds P i
          have hcfit : Fits h L ((2:ℤ)^P/(2*i+1:ℕ)) :=
            fits_twice_scale hwidth hc0 (by
              have hp0 : (0:ℤ)≤2^P := by positivity
              omega)
          rw [hone₂,hvalueD,floorDiv,ite_eq_right (by omega),wrap_of_fits hcfit] at hvalue₃
          have hvs₃ : Valid mem₃ s h L := valid_frozen hf₃ (by omega)
            (valid_frozen hf₂ (by omega) (valid_frozen hf₁ hs hvs))
          have hsval₃ : intVal mem₃ s h L=intVal mem s h L :=
            (value_frozen hf₃ (by omega)).trans
              ((value_frozen hf₂ (by omega)).trans (value_frozen hf₁ hs))
          have hvt₃ : Valid mem₃ (v₁-L) h L :=
            valid_frozen hf₃ (by omega) (valid_frozen hf₂ (by omega) hvalid₁)
          have htval₃ : intVal mem₃ (v₁-L) h L=logHornerInt P (intVal mem s h L) (i+1) n :=
            (value_frozen hf₃ (by omega)).trans ((value_frozen hf₂ (by omega)).trans hvalue₁)
          have hv₃w : v₃<2^w := by omega
          refine runs_seq_call_le hmC (vs:=[s,v₁-L,L,P,v₃]) (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨⟨_,_,_,_,_,rfl,hP,by omega,by omega,hvs₃,hvt₃⟩,
              hz₃,by change v₃+(11*L+1)<2^w; omega⟩
          · intro v₄ mem₄ pos₄ hp₄
            rcases hp₄ with ⟨hv₄,_,_,hf₄,hz₄,hvalid₄,hvalue₄⟩
            change v₄=v₃+(11*L+1) at hv₄
            change (∀ z<v₃,mem₄ z=mem₃ z) at hf₄
            change Valid mem₄ (v₃+10*L+1) h L at hvalid₄
            change intVal mem₄ (v₃+10*L+1) h L=wrap h L
              (intVal mem₃ s h L*intVal mem₃ (v₁-L) h L/(2:ℤ)^P) at hvalue₄
            have hptr₄ : v₃+10*L+1=v₄-L := by omega
            rw [hptr₄] at hvalid₄ hvalue₄
            obtain ⟨ht0,ht2⟩ := logHornerInt_bounds hs0 hs2 (i+1) n
            obtain ⟨hprod0,hprod1⟩ := logHornerInt_product_bounds hs0 hs2 ht0 ht2
            have hprodfit : Fits h L
                (intVal mem s h L*logHornerInt P (intVal mem s h L) (i+1) n/(2:ℤ)^P) :=
              fits_twice_scale hwidth hprod0 (by
                have hp0 : (0:ℤ)≤2^P := by positivity
                omega)
            rw [hsval₃,htval₃,wrap_of_fits hprodfit] at hvalue₄
            have hvc₄ : Valid mem₄ (v₃-L) h L := valid_frozen hf₄ (by omega) hvalid₃
            have hcval₄ : intVal mem₄ (v₃-L) h L=(2:ℤ)^P/(2*i+1:ℕ) :=
              (value_frozen hf₄ (by omega)).trans hvalue₃
            have hv₄w : v₄<2^w := by omega
            have hptr₃w : v₃-L<2^w := by omega
            have hptr₄w : v₄-L<2^w := by omega
            refine runs_seq_call_le haC (vs:=[v₃-L,v₄-L,L,0,v₄])
              (by eval_expr) (by wram_words) ?_ ?_
            · exact ⟨⟨_,_,_,_,_,rfl,by omega,by omega,by omega,hvc₄,hvalid₄⟩,
                hz₄,by change v₄+L<2^w; omega⟩
            · intro v mem₅ pos₅ hp₅
              rcases hp₅ with ⟨hv,_,_,hf₅,hz₅,hlist₅⟩
              change v=v₄+L at hv
              change (∀ z<v₄,mem₅ z=mem₄ z) at hf₅
              change ListAt mem₅ v₄ (digits h L
                (unsignedVal mem₄ (v₃-L) h L+unsignedVal mem₄ (v₄-L) h L+0)) at hlist₅
              have hfit : Fits h L (intVal mem₄ (v₃-L) h L+intVal mem₄ (v₄-L) h L+(0:ℕ)) := by
                rw [hcval₄,hvalue₄]
                simp only [Nat.cast_zero,add_zero]
                exact fits_twice_scale hwidth (add_nonneg hc0 hprod0) (by omega)
              have houtvalid := (addCarry_value hlist₅).1
              have hout := addCarry_value_of_fits hlist₅ hfit
              rw [hcval₄,hvalue₄] at hout
              simp only [Nat.cast_zero,add_zero] at hout
              have hvw : v<2^w := by omega
              refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
              · change v=heap+logHornerSpace L (n+1) ∧ heap≤v ∧
                  v≤heap+logHornerSpace L (n+1) ∧ (∀ z<heap,mem₅ z=mem z) ∧
                  ZeroFrom mem₅ v ∧ Valid mem₅ (heap+logHornerSpace L (n+1)-L) h L ∧
                  intVal mem₅ (heap+logHornerSpace L (n+1)-L) h L=
                    logHornerInt P (intVal mem s h L) i (n+1)
                have he : v=heap+logHornerSpace L (n+1) := by
                  rw [horner_space_step]
                  omega
                have heout : heap+logHornerSpace L (n+1)-L=v₄ := by
                  rw [horner_space_step]
                  omega
                refine ⟨he,by omega,by omega,?_,hz₅,?_,?_⟩
                · intro z hz
                  exact (hf₅ z (by omega)).trans ((hf₄ z (by omega)).trans
                    ((hf₃ z (by omega)).trans ((hf₂ z (by omega)).trans (hf₁ z hz))))
                · rw [heout]; exact houtvalid
                · rw [heout]; exact hout
              · simp only [logHornerContract,Contract.below,loadSmallContract,integerDivideContract,
                  fixedMultiplyContract,addCarryContract,heapContract,List.getD_cons_zero,
                  List.getD_cons_succ,Expr.size_reg,Expr.size_bin,Expr.size_const,
                  argsSize_cons,argsSize_nil,Nat.succ_eq_add_one,Nat.add_mul,Nat.mul_add]
                ring_nf
                omega

end MinCostFlow.Num
