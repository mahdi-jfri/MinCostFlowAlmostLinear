module

public import MinCostFlow.Num.IsNegative
public import MinCostFlow.Num.ExtendCopy
import MinCostFlow.Num.MultiplyFacts
import MinCostFlow.Num.FixedDivideFacts
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Extending signed blocks

Copy the low limbs and fill the high limbs with the sign limb. This preserves the
integer exactly and allows arithmetic to use a larger workspace. The cost is linear
in the destination length.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a,L,K,heap]`. -/
def signExtendBody (sign extend h : ℕ) : Stmt :=
  .call 4 sign [.reg 0,.reg 1] ;;
  .call 5 extend [.reg 0,.reg 1,.reg 2,.bin .mul (.const (base h-1)) (.reg 4),.reg 3] ;;
  .ret (.reg 5)

/-- Signed extension with sign-bit and copy helpers. -/
def signExtendModule (b h : ℕ) : List Stmt :=
  [signExtendBody (b+1) (b+2) h] ++ (isNegativeModule (b+1) h ++ extendCopyModule (b+2))

/-- Extend to any length at least the source length, preserving its signed value. -/
def signExtendContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a L K heap,args=[a,L,K,heap] ∧ L≤K ∧ a+L≤heap ∧ Valid mem a h L)
    (fun args mem mem' => Valid mem' (heapArg args) h (args.getD 2 0) ∧
      intVal mem' (heapArg args) h (args.getD 2 0)=intVal mem (args.getD 0 0) h (args.getD 1 0))
    (fun args _ => 30*args.getD 2 0+42) (fun args _ => args.getD 2 0)
  { C with post := fun args mem v mem' => v=heapArg args+args.getD 2 0 ∧ C.post args mem v mem' }

/-- Signed extension uses no random statement. -/
theorem signExtendModule_noRand (b h : ℕ) : ∀ s∈signExtendModule b h,s.NoRand := by
  intro s hs
  simp only [signExtendModule,List.mem_append,List.mem_singleton,isNegativeModule,extendCopyModule] at hs
  rcases hs with rfl | rfl | rfl
  · simp [signExtendBody,Stmt.NoRand]
  · exact isNegativeBody_noRand _
  · exact extendCopyBody_noRand _

/-- Signed extension meets its exact heap and value contract. -/
theorem signExtend_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 1<2^w) (hb : base h<2^w)
    (hp : p.HasAt b (signExtendModule b h)) : MeetsContract w p b (signExtendContract w h) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hs := isNegative_meetsContract hh hw hb (hasAt_append_left ht)
  have he := hasAt_append_right ht
  change p.HasAt (b+2) _ at he
  have hc := extendCopy_meetsContract (h:=h) hw he
  have hentry : p.procs[b]?=some (signExtendBody (b+1) (b+2) h) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a,L,K,heap,rfl,hLK,ha,hvalid⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+K<2^w at hbound
  have haw : a<2^w := hwords a (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hKw : K<2^w := hwords K (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have hfillw : base h-1<2^w := by omega
  apply runs_start_le
  unfold signExtendBody
  refine runs_seq_call_le hs (vs:=[a,L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨a,L,rfl,by omega,hvalid⟩
  · intro sign mem₁ pos₁ hp₁
    rcases hp₁ with ⟨hmem,hsign⟩
    subst mem₁
    change sign=if intVal mem a h L<0 then 1 else 0 at hsign
    have hf : (base h-1)*sign=(if intVal mem a h L<0 then base h-1 else 0) := by
      rw [hsign]; split_ifs <;> simp
    have hfb : (base h-1)*sign<base h := by rw [hf]; split_ifs <;> have := base_pos h <;> omega
    have hfw : (base h-1)*sign<2^w := lt_trans hfb hb
    refine runs_seq_call_le hc (vs:=[a,L,K,(base h-1)*sign,heap]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨a,L,K,_,heap,rfl,hLK,ha,hfb,hvalid⟩,hz,hbound⟩
    · intro v mem₂ pos₂ hp₂
      rcases hp₂ with ⟨hv,hlo,hhi,hframe,hz₂,hlist⟩
      change v=heap+K at hv
      change ListAt mem₂ heap (extendedLimbs mem a ((base h-1)*sign) L K) at hlist
      have hvalid₂ := valid_listAt hlist (extendedLimbs_lt hvalid hfb)
      rw [extendedLimbs_length] at hvalid₂
      rw [hf] at hlist
      have hres := extended_residue hvalid hLK hlist
      have hvalue : intVal mem₂ heap h K=intVal mem a h L := by
        calc
          _=wrap h K (intVal mem₂ heap h K) := (wrap_of_fits (intVal_fits hvalid₂)).symm
          _=wrap h K (intVal mem a h L) := wrap_congr ((signedVal_emod h K _).trans hres)
          _=_ := wrap_of_fits (fits_of_length_le hLK (intVal_fits hvalid))
      have hvw : v<2^w := by omega
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · exact ⟨hv,hlo,hhi,hframe,hz₂,hvalid₂,hvalue⟩
      · simp only [signExtendContract,isNegativeContract,extendCopyContract,heapContract,
          List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,
          argsSize_cons,argsSize_nil]
        omega

end MinCostFlow.Num
