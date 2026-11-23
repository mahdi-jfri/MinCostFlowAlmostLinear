module

public import MinCostFlow.Num.ExpHornerIntegerFacts
public import MinCostFlow.Num.Copy
public import MinCostFlow.Num.FixedMultiply
public import MinCostFlow.Num.LoadSmall
public import MinCostFlow.Num.IntegerDivide
public import MinCostFlow.Num.AddCarry
import MinCostFlow.Num.LogHornerIntegerFacts
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Fixed-point exponential Horner evaluation

The last Taylor coefficient is one. Each recursive step multiplies the tail
by the argument, divides by the next coefficient index, and adds one. The two
divisions round down exactly as in the real rounding analysis.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Space for one tail block and the arithmetic of each series step. -/
def expHornerSpace (L n : ℕ) : ℕ := n*(13*L+integerDivideSpace L+1)+L

/-- Arguments `[x,one,L,P,i,n,heap]`. -/
def expHornerBody (self copy mul load divide add : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 5) (.const 0))
    (.call 7 copy [.reg 1,.reg 2,.reg 6] ;; .ret (.reg 7))
    (.call 7 self [.reg 0,.reg 1,.reg 2,.reg 3,.bin .add (.reg 4) (.const 1),
        .bin .sub (.reg 5) (.const 1),.reg 6] ;;
     .call 8 mul [.reg 0,.bin .sub (.reg 7) (.reg 2),.reg 2,.reg 3,.reg 7] ;;
     .call 9 load [.bin .add (.reg 4) (.const 1),.reg 2,.reg 8] ;;
     .call 10 divide [.bin .sub (.reg 8) (.reg 2),.reg 8,.reg 2,.reg 9] ;;
     .call 11 add [.reg 1,.bin .sub (.reg 10) (.reg 2),.reg 2,.const 0,.reg 10] ;;
     .ret (.reg 11))

/-- Reduced exponential series and its closed arithmetic dependencies. -/
def expHornerModule (b h : ℕ) : List Stmt :=
  [expHornerBody b (b+1) (b+2) (b+13) (b+14) (b+39)] ++
    (copyModule (b+1) ++ (fixedMultiplyModule (b+2) h ++
      (loadSmallModule (b+13) h ++ (integerDivideModule (b+14) h ++ addCarryModule (b+39) h))))

/-- The input is between zero and one half. All intermediate results fit
when there are four spare bits beyond the precision. -/
def expHornerContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a one L P i n heap,args=[a,one,L,P,i,n,heap] ∧ h∣P ∧
      P+4≤h*L ∧ a+L≤heap ∧ one+L≤heap ∧ Valid mem a h L ∧ Valid mem one h L ∧
      intVal mem one h L=(2:ℤ)^P ∧ 0 ≤ intVal mem a h L ∧
      2*intVal mem a h L≤(2:ℤ)^P ∧ i+n+1≤2^P ∧ i+n+1<2^w)
    (fun args mem mem' =>
      Valid mem' (heapArg args+expHornerSpace (args.getD 2 0) (args.getD 5 0)-args.getD 2 0) h (args.getD 2 0) ∧
      intVal mem' (heapArg args+expHornerSpace (args.getD 2 0) (args.getD 5 0)-args.getD 2 0) h (args.getD 2 0)=
        expHornerInt (args.getD 3 0) (intVal mem (args.getD 0 0) h (args.getD 2 0))
          (args.getD 4 0) (args.getD 5 0))
    (fun args _ => args.getD 5 0*(500*(args.getD 2 0)^2+2000*args.getD 2 0+2000)+17*args.getD 2 0+30)
    (fun args _ => expHornerSpace (args.getD 2 0) (args.getD 5 0))
  { C with post := fun args mem v mem' =>
    v=heapArg args+expHornerSpace (args.getD 2 0) (args.getD 5 0) ∧ C.post args mem v mem' }

/-- The series module is deterministic. -/
theorem expHornerModule_noRand (b h : ℕ) : ∀ s∈expHornerModule b h,s.NoRand := by
  intro s hs
  simp only [expHornerModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hc | hm | hl | hd | ha
  · simp [expHornerBody,Stmt.NoRand]
  · have he : s=copyBody := by simpa [copyModule] using hc
    subst s
    exact copyBody_noRand
  · exact fixedMultiplyModule_noRand _ _ _ hm
  · have he : s=loadSmallBody (b+13) h := by simpa [loadSmallModule] using hl
    subst s
    exact loadSmallBody_noRand _ _
  · exact integerDivideModule_noRand _ _ _ hd
  · have he : s=addCarryBody (b+39) h := by simpa [addCarryModule] using ha
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
    (hl : ListAt mem a (digits h L n)) (hf : Fits h L (n:ℤ)) : intVal mem a h L=(n:ℤ) := by
  rw [(loadSmall_value hl).2.2]
  have he : residue h L (n:ℤ)=n%capacity h L := by
    simp only [residue,← Int.natCast_mod,Int.toNat_natCast]
  rw [← he]
  exact wrap_of_fits hf

private theorem exp_space_step (L n : ℕ) :
    expHornerSpace L (n+1)=expHornerSpace L n+(11*L+1)+L+integerDivideSpace L+L := by
  unfold expHornerSpace
  ring

set_option maxHeartbeats 600000 in
/-- The exponential Horner procedure meets its exact rounded-integer contract,
with quadratic cost per term and no overflowing intermediate. -/
theorem expHorner_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (expHornerModule b h)) :
    MeetsContract w p b (expHornerContract w h) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hc := hasAt_append_left ht
  have ht₂ := hasAt_append_right ht
  change p.HasAt (b+2) _ at ht₂
  have hm := hasAt_append_left ht₂
  have ht₃ := hasAt_append_right ht₂
  change p.HasAt (b+13) _ at ht₃
  have hl := hasAt_append_left ht₃
  have ht₄ := hasAt_append_right ht₃
  change p.HasAt (b+14) _ at ht₄
  have hd := hasAt_append_left ht₄
  have ha := hasAt_append_right ht₄
  change p.HasAt (b+39) _ at ha
  have hb := base_lt_word (show 2*h+2≤w by omega)
  have hw1 : 1<2^w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  have hw0 : w≠0 := by omega
  have hcC := copy_meetsContract (h:=h) hw1 hc
  have hmC := fixedMultiply_meetsContract hh (show 2*h+2≤w by omega) hm
  have hlC := loadSmall_meetsContract hw1 hb hl
  have hdC := integerDivide_meetsContract hh hw hd
  have haC := addCarry_meetsContract hh (show 2*h+2≤w by omega) ha
  apply meetsContract_of_rec (fun args _ => args.getD 5 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨⟨a,one,L,P,i,n,heap,rfl,hP,hwidth,ha,ho,hva,hvo,hone,hY0,hY1,hden,hdenw⟩,hz,hbound⟩
  change n=k at hk
  subst k
  change ZeroFrom mem heap at hz
  change heap+expHornerSpace L n<2^w at hbound
  have haw : a<2^w := hwords a (by simp)
  have how : one<2^w := hwords one (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPw : P<2^w := hwords P (by simp)
  have hiw : i<2^w := hwords i (by simp)
  have hnw : n<2^w := hwords n (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  apply runs_start_le
  unfold expHornerBody
  wram_step
  · have hn0 : n=0 := by simpa [startState] using hcond
    subst n
    have hend : heap+L<2^w := by simpa [expHornerSpace] using hbound
    refine runs_seq_call_le hcC (vs:=[one,L,heap]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,rfl,ho,hvo⟩,hz,hend⟩
    · intro v mem' pos' hp'
      rcases hp' with ⟨hv,hlo,hhi,hf,hz',_,hvalid,hvalue⟩
      change v=heap+L at hv
      change (∀ z<heap,mem' z=mem z) at hf
      change Valid mem' heap h L at hvalid
      change intVal mem' heap h L=intVal mem one h L at hvalue
      have hvw : v<2^w := by omega
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change v=heap+expHornerSpace L 0 ∧ heap≤v ∧ v≤heap+expHornerSpace L 0 ∧
          (∀ z<heap,mem' z=mem z) ∧ ZeroFrom mem' v ∧
          Valid mem' (heap+expHornerSpace L 0-L) h L ∧
          intVal mem' (heap+expHornerSpace L 0-L) h L=expHornerInt P (intVal mem a h L) i 0
        simp only [expHornerSpace,zero_mul,zero_add,Nat.add_sub_cancel,expHornerInt]
        exact ⟨hv,by omega,by omega,hf,hz',hvalid,hvalue.trans hone⟩
      · simp only [expHornerContract,copyContract,heapContract,List.getD_cons_zero,List.getD_cons_succ,
          Expr.size_reg,Expr.size_bin,Expr.size_const,argsSize_cons,argsSize_nil]
        omega
  · have hn0 : n≠0 := by simpa [startState] using hcond
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    rw [exp_space_step] at hbound
    have hipw : i+1<2^w := by omega
    have hn' : n<2^w := by omega
    have hrec : MeetsContract w p b
        ((expHornerContract w h).below (fun args _ => args.getD 5 0) (n+1)) := ih
    refine runs_seq_call_le hrec (vs:=[a,one,L,P,i+1,n,heap])
      (by eval_expr <;> simp [Expr.eval,BinOp.eval,startState,hw0,hn']) (by wram_words) ?_ ?_
    · refine ⟨⟨⟨_,_,_,_,_,_,_,rfl,hP,hwidth,ha,ho,hva,hvo,hone,hY0,hY1,?_,?_⟩,
        hz,by change heap+expHornerSpace L n<2^w; omega⟩,by change n<n+1; omega⟩
      · convert hden using 1 <;> omega
      · convert hdenw using 1 <;> omega
    · intro v₁ mem₁ pos₁ hp₁
      rcases hp₁ with ⟨hv₁,_,_,hf₁,hz₁,hvalid₁,hvalue₁⟩
      change v₁=heap+expHornerSpace L n at hv₁
      change (∀ z<heap,mem₁ z=mem z) at hf₁
      change Valid mem₁ (heap+expHornerSpace L n-L) h L at hvalid₁
      change intVal mem₁ (heap+expHornerSpace L n-L) h L=
        expHornerInt P (intVal mem a h L) (i+1) n at hvalue₁
      rw [← hv₁] at hvalid₁ hvalue₁
      have hlow : L≤v₁ := by rw [hv₁]; unfold expHornerSpace; omega
      have hva₁ := valid_frozen hf₁ ha hva
      have ha₁ : intVal mem₁ a h L=intVal mem a h L := value_frozen hf₁ ha
      have hv₁w : v₁<2^w := by omega
      have hptr₁w : v₁-L<2^w := by omega
      refine runs_seq_call_le hmC (vs:=[a,v₁-L,L,P,v₁]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨_,_,_,_,_,rfl,hP,by omega,by omega,hva₁,hvalid₁⟩,
          hz₁,by change v₁+(11*L+1)<2^w; omega⟩
      · intro v₂ mem₂ pos₂ hp₂
        rcases hp₂ with ⟨hv₂,_,_,hf₂,hz₂,hvalid₂,hvalue₂⟩
        change v₂=v₁+(11*L+1) at hv₂
        change (∀ z<v₁,mem₂ z=mem₁ z) at hf₂
        change Valid mem₂ (v₁+10*L+1) h L at hvalid₂
        change intVal mem₂ (v₁+10*L+1) h L=wrap h L
          (intVal mem₁ a h L*intVal mem₁ (v₁-L) h L/(2:ℤ)^P) at hvalue₂
        have hptr₂ : v₁+10*L+1=v₂-L := by omega
        rw [hptr₂,ha₁,hvalue₁] at hvalue₂
        rw [hptr₂] at hvalid₂
        obtain ⟨⟨hM0,hM1⟩,hQ0,hQ1⟩ := expHornerInt_step_bounds hY0 hY1 i n
        have hscale0 : (0:ℤ)≤(2:ℤ)^P := by positivity
        have hMfit : Fits h L (intVal mem a h L*expHornerInt P (intVal mem a h L) (i+1) n/(2:ℤ)^P) :=
          fits_twice_scale hwidth hM0 (by omega)
        rw [wrap_of_fits hMfit] at hvalue₂
        have hv₂w : v₂<2^w := by omega
        have hptr₂w : v₂-L<2^w := by omega
        refine runs_seq_call_le hlC (vs:=[i+1,L,v₂]) (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨⟨_,_,_,rfl⟩,hz₂,by change v₂+L<2^w; omega⟩
        · intro v₃ mem₃ pos₃ hp₃
          rcases hp₃ with ⟨hv₃,_,_,hf₃,hz₃,hlist₃⟩
          change v₃=v₂+L at hv₃
          change (∀ z<v₂,mem₃ z=mem₂ z) at hf₃
          change ListAt mem₃ v₂ (digits h L (i+1)) at hlist₃
          have hd0 : (0:ℤ)<(i+1:ℕ) := by omega
          have hdcap : (i+1:ℕ)≤(2:ℤ)^P := by
            have hh : i+1≤2^P := le_trans (by omega) hden
            exact_mod_cast hh
          have hdfit : Fits h L (i+1:ℕ) := fits_twice_scale hwidth (by omega) (by omega)
          have hvalidD := (loadSmall_value hlist₃).1
          have hvalueD := loadSmall_decode hlist₃ hdfit
          have hvM₃ := valid_frozen hf₃ (by omega) hvalid₂
          have hM₃ : intVal mem₃ (v₂-L) h L=
              intVal mem a h L*expHornerInt P (intVal mem a h L) (i+1) n/(2:ℤ)^P :=
            (value_frozen hf₃ (by omega)).trans hvalue₂
          have hv₃w : v₃<2^w := by omega
          refine runs_seq_call_le hdC (vs:=[v₂-L,v₂,L,v₃]) (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨⟨_,_,_,_,rfl,by omega,by omega,hvM₃,hvalidD,by rw [hvalueD]; omega⟩,
              hz₃,by change v₃+integerDivideSpace L<2^w; omega⟩
          · intro v₄ mem₄ pos₄ hp₄
            rcases hp₄ with ⟨hv₄,_,_,hf₄,hz₄,hvalid₄,hvalue₄⟩
            change v₄=v₃+integerDivideSpace L at hv₄
            change (∀ z<v₃,mem₄ z=mem₃ z) at hf₄
            change Valid mem₄ (v₃+2*L+unsignedDivideSpace L) h L at hvalid₄
            change intVal mem₄ (v₃+2*L+unsignedDivideSpace L) h L=
              wrap h L (floorDiv (intVal mem₃ (v₂-L) h L) (intVal mem₃ v₂ h L)) at hvalue₄
            have hptr₄ : v₃+2*L+unsignedDivideSpace L=v₄-L := by unfold integerDivideSpace at hv₄; omega
            rw [hptr₄] at hvalid₄ hvalue₄
            have hQfit : Fits h L ((intVal mem a h L*expHornerInt P (intVal mem a h L) (i+1) n/
                (2:ℤ)^P)/(i+1:ℕ)) := fits_twice_scale hwidth hQ0 (by omega)
            rw [hM₃,hvalueD,floorDiv,ite_eq_right (by omega),wrap_of_fits hQfit] at hvalue₄
            have hvo₄ := valid_frozen hf₄ (by omega)
              (valid_frozen hf₃ (by omega) (valid_frozen hf₂ (by omega) (valid_frozen hf₁ ho hvo)))
            have hone₄ : intVal mem₄ one h L=(2:ℤ)^P :=
              (value_frozen hf₄ (by omega)).trans ((value_frozen hf₃ (by omega)).trans
                ((value_frozen hf₂ (by omega)).trans ((value_frozen hf₁ ho).trans hone)))
            have hv₄w : v₄<2^w := by omega
            have hptr₄w : v₄-L<2^w := by omega
            refine runs_seq_call_le haC (vs:=[one,v₄-L,L,0,v₄]) (by eval_expr) (by wram_words) ?_ ?_
            · exact ⟨⟨_,_,_,_,_,rfl,by omega,by omega,by omega,hvo₄,hvalid₄⟩,
                hz₄,by change v₄+L<2^w; omega⟩
            · intro v mem₅ pos₅ hp₅
              rcases hp₅ with ⟨hv,_,_,hf₅,hz₅,hlist₅⟩
              change v=v₄+L at hv
              change (∀ z<v₄,mem₅ z=mem₄ z) at hf₅
              change ListAt mem₅ v₄ (digits h L
                (unsignedVal mem₄ one h L+unsignedVal mem₄ (v₄-L) h L+0)) at hlist₅
              have hsumfit : Fits h L (intVal mem₄ one h L+intVal mem₄ (v₄-L) h L+(0:ℕ)) := by
                rw [hone₄,hvalue₄]
                simp only [Nat.cast_zero,add_zero]
                exact fits_twice_scale hwidth (by omega) (by omega)
              have hvalid₅ := (addCarry_value hlist₅).1
              have hvalue₅ := addCarry_value_of_fits hlist₅ hsumfit
              rw [hone₄,hvalue₄] at hvalue₅
              simp only [Nat.cast_zero,add_zero] at hvalue₅
              have hvw : v<2^w := by omega
              refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
              · change v=heap+expHornerSpace L (n+1) ∧ heap≤v ∧ v≤heap+expHornerSpace L (n+1) ∧
                  (∀ z<heap,mem₅ z=mem z) ∧ ZeroFrom mem₅ v ∧
                  Valid mem₅ (heap+expHornerSpace L (n+1)-L) h L ∧
                  intVal mem₅ (heap+expHornerSpace L (n+1)-L) h L=expHornerInt P (intVal mem a h L) i (n+1)
                have he : v=heap+expHornerSpace L (n+1) := by rw [exp_space_step]; omega
                have hout : heap+expHornerSpace L (n+1)-L=v₄ := by rw [← he]; omega
                refine ⟨he,by omega,by omega,?_,hz₅,?_,?_⟩
                · intro z hz
                  exact (hf₅ z (by omega)).trans ((hf₄ z (by omega)).trans ((hf₃ z (by omega)).trans
                    ((hf₂ z (by omega)).trans (hf₁ z hz))))
                · rw [hout]; exact hvalid₅
                · rw [hout]; exact hvalue₅
              · simp only [expHornerContract,Contract.below,fixedMultiplyContract,loadSmallContract,
                  integerDivideContract,addCarryContract,heapContract,List.getD_cons_zero,
                  List.getD_cons_succ,Expr.size_reg,Expr.size_bin,Expr.size_const,argsSize_cons,argsSize_nil,
                  Nat.succ_eq_add_one,Nat.add_mul,Nat.mul_add]
                ring_nf
                omega

end MinCostFlow.Num
