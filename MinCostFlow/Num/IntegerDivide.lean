module

public import MinCostFlow.Num.Absolute
public import MinCostFlow.Num.UnsignedDivide
public import MinCostFlow.Num.RestoreQuotient
public import MinCostFlow.Num.DivisionSigns
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Signed integer floor division

Convert both operands to unsigned magnitudes, run long division, and restore the
quotient sign with the remainder correction. The contract states mathematical floor
for either divisor sign and wraps a result that exceeds the signed output range.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Magnitudes, unsigned division workspace, and the final signed quotient. -/
def integerDivideSpace (L : ℕ) : ℕ := unsignedDivideSpace L + 3*L

/-- Arguments `[a,d,L,heap]`. -/
def integerDivideBody (sign absolute divide restore : ℕ) : Stmt :=
  .call 4 sign [.reg 0,.reg 2] ;;
  .call 5 sign [.reg 1,.reg 2] ;;
  .call 6 absolute [.reg 0,.reg 2,.reg 3] ;;
  .call 7 absolute [.reg 1,.reg 2,.reg 6] ;;
  .call 8 divide [.reg 3,.reg 6,.reg 2,.reg 7] ;;
  .call 9 restore [.bin .add (.bin .add (.reg 7) (.reg 2)) (.const 1),
    .bin .sub (.reg 8) (.bin .add (.reg 2) (.const 1)),.reg 2,
    .bin .sub (.const 1) (.bin .eq (.reg 4) (.reg 5)),.reg 8] ;;
  .ret (.reg 9)

/-- Signed division and its linked arithmetic procedures. -/
def integerDivideModule (b h : ℕ) : List Stmt :=
  [integerDivideBody (b+1) (b+2) (b+7) (b+21)] ++
    (isNegativeModule (b+1) h ++ (absoluteModule (b+2) h ++
      (unsignedDivideModule (b+7) h ++ restoreQuotientModule (b+21) h)))

/-- Nonzero signed divisor; output has explicit wrap semantics and exact allocation. -/
def integerDivideContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a d L heap, args=[a,d,L,heap] ∧ a+L≤heap ∧ d+L≤heap ∧
      Valid mem a h L ∧ Valid mem d h L ∧ intVal mem d h L≠0)
    (fun args mem mem' =>
      Valid mem' (heapArg args+2*args.getD 2 0+unsignedDivideSpace (args.getD 2 0)) h (args.getD 2 0) ∧
      intVal mem' (heapArg args+2*args.getD 2 0+unsignedDivideSpace (args.getD 2 0)) h (args.getD 2 0) =
        wrap h (args.getD 2 0) (floorDiv (intVal mem (args.getD 0 0) h (args.getD 2 0))
          (intVal mem (args.getD 1 0) h (args.getD 2 0))))
    (fun args _ => args.getD 2 0*(300*args.getD 2 0+644)+180*args.getD 2 0+400)
    (fun args _ => integerDivideSpace (args.getD 2 0))
  { C with post := fun args mem v mem' => v=heapArg args+integerDivideSpace (args.getD 2 0) ∧ C.post args mem v mem' }

/-- Signed floor division uses no random statement. -/
theorem integerDivideModule_noRand (b h : ℕ) : ∀ s ∈ integerDivideModule b h, s.NoRand := by
  intro s hs
  simp only [integerDivideModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hsign | habs | hdiv | hrestore
  · simp [integerDivideBody,Stmt.NoRand]
  · have he : s=isNegativeBody h := by simpa [isNegativeModule] using hsign
    subst s; exact isNegativeBody_noRand _
  · exact absoluteModule_noRand _ _ _ habs
  · exact unsignedDivideModule_noRand _ _ _ hdiv
  · exact restoreQuotientModule_noRand _ _ _ hrestore

/-- Signed floor division meets its heap contract with quadratic cost. -/
theorem integerDivide_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (integerDivideModule b h)) :
    MeetsContract w p b (integerDivideContract w h) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hsign := hasAt_append_left ht
  have ht₂ := hasAt_append_right ht
  change p.HasAt (b+2) _ at ht₂
  have habs := hasAt_append_left ht₂
  have ht₃ := hasAt_append_right ht₂
  change p.HasAt (b+7) _ at ht₃
  have hdiv := hasAt_append_left ht₃
  have hrestore := hasAt_append_right ht₃
  change p.HasAt (b+21) _ at hrestore
  have hb := base_lt_word (show 2*h+2≤w by omega)
  have hw1 : 1<2^w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  have hs := isNegative_meetsContract hh hw1 hb hsign
  have haC := absolute_meetsContract hh hw1 hb habs
  have hdC := unsignedDivide_meetsContract hh hw hdiv
  have hrC := restoreQuotient_meetsContract hw1 hb hrestore
  have hentry : p.procs[b]? = some (integerDivideBody (b+1) (b+2) (b+7) (b+21)) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a,d,L,heap,rfl,ha,hd,hva,hvd,hne⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+integerDivideSpace L<2^w at hbound
  have hbound' : heap+unsignedDivideSpace L+3*L<2^w := by
    simpa only [integerDivideSpace,Nat.add_assoc] using hbound
  have haw : a<2^w := hwords a (by simp)
  have hdw : d<2^w := hwords d (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have hspace : 2≤unsignedDivideSpace L := by unfold unsignedDivideSpace; omega
  apply runs_start_le
  unfold integerDivideBody
  refine runs_seq_call_le hs (vs:=[a,L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨a,L,rfl,by omega,hva⟩
  · intro sA mem₀ pos₀ hp₀
    rcases hp₀ with ⟨hm₀,hsA⟩
    subst mem₀
    change sA=if intVal mem a h L<0 then 1 else 0 at hsA
    have hsAw : sA<2^w := by split_ifs at hsA <;> omega
    refine runs_seq_call_le hs (vs:=[d,L]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨d,L,rfl,by omega,hvd⟩
    · intro sD mem₀ pos₀ hp₀
      rcases hp₀ with ⟨hm₀,hsD⟩
      subst mem₀
      change sD=if intVal mem d h L<0 then 1 else 0 at hsD
      have hsDw : sD<2^w := by split_ifs at hsD <;> omega
      refine runs_seq_call_le haC (vs:=[a,L,heap]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨a,L,heap,rfl,ha,hva⟩,hz,by change heap+L<2^w; omega⟩
      · intro v₁ mem₁ pos₁ hp₁
        rcases hp₁ with ⟨hv₁,hlo₁,hhi₁,hf₁,hz₁,hvalid₁,hvalue₁⟩
        change v₁=heap+L at hv₁
        change (∀ z<heap,mem₁ z=mem z) at hf₁
        change Valid mem₁ heap h L at hvalid₁
        change unsignedVal mem₁ heap h L=(intVal mem a h L).natAbs at hvalue₁
        have hvdw : Valid mem₁ d h L := by intro i hi; rw [hf₁ _ (by omega)]; exact hvd i hi
        have hde : intVal mem₁ d h L=intVal mem d h L := intVal_congr (fun i hi => hf₁ _ (by omega))
        have hv₁w : v₁<2^w := by omega
        refine runs_seq_call_le haC (vs:=[d,L,v₁]) (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨⟨d,L,v₁,rfl,by omega,hvdw⟩,hz₁,by change v₁+L<2^w; omega⟩
        · intro v₂ mem₂ pos₂ hp₂
          rcases hp₂ with ⟨hv₂,hlo₂,hhi₂,hf₂,hz₂,hvalid₂,hvalue₂⟩
          change v₂=v₁+L at hv₂
          change (∀ z<v₁,mem₂ z=mem₁ z) at hf₂
          change Valid mem₂ v₁ h L at hvalid₂
          change unsignedVal mem₂ v₁ h L=(intVal mem₁ d h L).natAbs at hvalue₂
          rw [hde] at hvalue₂
          have hvalidA : Valid mem₂ heap h L := by intro i hi; rw [hf₂ _ (by omega)]; exact hvalid₁ i hi
          have hvalueA : unsignedVal mem₂ heap h L=(intVal mem a h L).natAbs :=
            (unsignedVal_congr (fun i hi => hf₂ _ (by omega))).trans hvalue₁
          have hV : 0<unsignedVal mem₂ v₁ h L := by rw [hvalue₂]; exact Int.natAbs_pos.mpr hne
          have hv₂w : v₂<2^w := by omega
          refine runs_seq_call_le hdC (vs:=[heap,v₁,L,v₂]) (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨⟨heap,v₁,L,v₂,rfl,by omega,by omega,hvalidA,hvalid₂,hV⟩,hz₂,
              by change v₂+unsignedDivideSpace L<2^w; omega⟩
          · intro v₃ mem₃ pos₃ hp₃
            rcases hp₃ with ⟨hv₃,hlo₃,hhi₃,hf₃,hz₃,hvalidQ,hvalueQ,hvalidR,hvalueR⟩
            change v₃=v₂+unsignedDivideSpace L at hv₃
            change (∀ z<v₂,mem₃ z=mem₂ z) at hf₃
            change Valid mem₃ (v₂+L+1) h L at hvalidQ
            change unsignedVal mem₃ (v₂+L+1) h L=unsignedVal mem₂ heap h L / unsignedVal mem₂ v₁ h L at hvalueQ
            change Valid mem₃ (v₂+unsignedDivideSpace L-(L+1)) h (L+1) at hvalidR
            change unsignedVal mem₃ (v₂+unsignedDivideSpace L-(L+1)) h (L+1)=unsignedVal mem₂ heap h L % unsignedVal mem₂ v₁ h L at hvalueR
            rw [hvalueA,hvalue₂] at hvalueQ hvalueR
            have hflagw : 1-(if sA=sD then 1 else 0)<2^w := by split_ifs <;> omega
            have hqptrw : v₂+L+1<2^w := by unfold unsignedDivideSpace at hv₃; omega
            have hrptrw : v₃-(L+1)<2^w := by omega
            have hv₃w : v₃<2^w := by omega
            refine runs_seq_call_le hrC
              (vs:=[v₂+L+1,v₃-(L+1),L,1-(if sA=sD then 1 else 0),v₃])
              (by eval_expr) (by wram_words) ?_ ?_
            · refine ⟨⟨v₂+L+1,v₃-(L+1),L,1-(if sA=sD then 1 else 0),v₃,rfl,?_,by omega,
                by split_ifs <;> omega,hvalidQ,?_⟩,hz₃,by change v₃+L<2^w; omega⟩
              · unfold unsignedDivideSpace at hv₃; omega
              · simpa only [hv₃] using hvalidR
            · intro v mem₄ pos₄ hp₄
              rcases hp₄ with ⟨hv,hlo,hhi,hf₄,hz₄,hvalid,hvalue⟩
              change v=v₃+L at hv
              change (∀ z<v₃,mem₄ z=mem₃ z) at hf₄
              change Valid mem₄ v₃ h L at hvalid
              change intVal mem₄ v₃ h L=wrap h L (restoredQuotient (unsignedVal mem₃ (v₂+L+1) h L)
                (unsignedVal mem₃ (v₃-(L+1)) h (L+1)) (1-(if sA=sD then 1 else 0))) at hvalue
              have hrval : unsignedVal mem₃ (v₃-(L+1)) h (L+1)=
                  (intVal mem a h L).natAbs % (intVal mem d h L).natAbs := by simpa only [hv₃] using hvalueR
              rw [hvalueQ,hrval] at hvalue
              have hsame : (sA=sD) ↔ (intVal mem a h L<0 ↔ intVal mem d h L<0) := by
                rw [hsA,hsD]
                by_cases hx : intVal mem a h L<0 <;> by_cases hy : intVal mem d h L<0 <;> simp [hx,hy]
              have hmath : restoredQuotient ((intVal mem a h L).natAbs / (intVal mem d h L).natAbs)
                  ((intVal mem a h L).natAbs % (intVal mem d h L).natAbs) (1-(if sA=sD then 1 else 0)) =
                  floorDiv (intVal mem a h L) (intVal mem d h L) := by
                rw [floorDiv_abs _ _ hne]
                by_cases he : sA=sD
                · simp [restoredQuotient,he,hsame.mp he]
                · have he' : ¬ (intVal mem a h L<0 ↔ intVal mem d h L<0) := by
                    intro hx; exact he (hsame.mpr hx)
                  simp [restoredQuotient,he,he']
              rw [hmath] at hvalue
              have hvw : v<2^w := by omega
              refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
              · change v=heap+integerDivideSpace L ∧ heap≤v ∧ v≤heap+integerDivideSpace L ∧
                  (∀ z<heap,mem₄ z=mem z) ∧ ZeroFrom mem₄ v ∧
                  Valid mem₄ (heap+2*L+unsignedDivideSpace L) h L ∧
                  intVal mem₄ (heap+2*L+unsignedDivideSpace L) h L=
                    wrap h L (floorDiv (intVal mem a h L) (intVal mem d h L))
                have he : v₃=heap+2*L+unsignedDivideSpace L := by omega
                have hvexact : v=heap+integerDivideSpace L := by unfold integerDivideSpace; omega
                refine ⟨hvexact,by omega,by omega,?_,hz₄,?_,?_⟩
                · intro z hz
                  exact (hf₄ z (by omega)).trans ((hf₃ z (by omega)).trans ((hf₂ z (by omega)).trans (hf₁ z hz)))
                · simpa only [he] using hvalid
                · simpa only [he] using hvalue
              · simp only [integerDivideContract,isNegativeContract,absoluteContract,unsignedDivideContract,
                  restoreQuotientContract,heapContract,List.getD_cons_zero,List.getD_cons_succ,
                  Expr.size_reg,Expr.size_const,Expr.size_bin,argsSize_cons,argsSize_nil]
                omega

end MinCostFlow.Num
