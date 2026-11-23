module

public import MinCostFlow.Num.Multiply
public import MinCostFlow.Num.Copy
public import MinCostFlow.Num.ShiftFacts
public import MinCostFlow.Num.IPM.FixedPointFacts
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Exact multiplication by an integer coefficient

The cost term of an IPM gradient multiplies a fixed-point number by an
integer. We use the signed double-width product and retain its low limbs.
If the result fits the original width, this introduces no rounding and
keeps the original fixed-point precision.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[integer,fixedPoint,L,heap]`. -/
def integerTimesBody (mul copy : ℕ) : Stmt :=
  .call 4 mul [.reg 0,.reg 1,.reg 2,.reg 3] ;;
  .call 5 copy [.bin .add (.reg 3) (.bin .mul (.const 4) (.reg 2)),.reg 2,.reg 4] ;;
  .ret (.reg 5)

/-- Exact double-width multiplication followed by a low-limb copy. -/
def integerTimesModule (b h : ℕ) : List Stmt :=
  [integerTimesBody (b+1) (b+6)] ++ (multiplyModule (b+1) h ++ copyModule (b+6))

/-- A fitting integer product is returned exactly in `L` limbs at `heap+6L`.
The procedure uses `7L` fresh cells and at most `152L²+207L+200` steps. -/
def integerTimesContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a d L heap,args=[a,d,L,heap] ∧ a+L≤heap ∧ d+L≤heap ∧
      Valid mem a h L ∧ Valid mem d h L ∧ Fits h L (intVal mem a h L*intVal mem d h L))
    (fun args mem mem' =>
      Valid mem' (heapArg args+6*args.getD 2 0) h (args.getD 2 0) ∧
      intVal mem' (heapArg args+6*args.getD 2 0) h (args.getD 2 0)=
        intVal mem (args.getD 0 0) h (args.getD 2 0)*intVal mem (args.getD 1 0) h (args.getD 2 0))
    (fun args _ => 152*(args.getD 2 0)^2+207*args.getD 2 0+200)
    (fun args _ => 7*args.getD 2 0)
  {C with post := fun args mem v mem' => v=heapArg args+7*args.getD 2 0 ∧ C.post args mem v mem'}

/-- Integer coefficient multiplication has no random statements. -/
theorem integerTimesModule_noRand (b h : ℕ) : ∀ s∈integerTimesModule b h,s.NoRand := by
  intro s hs
  simp only [integerTimesModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hm | hc
  · simp [integerTimesBody,Stmt.NoRand]
  · exact multiplyModule_noRand _ _ _ hm
  · simp only [copyModule,List.mem_singleton] at hc
    subst s
    exact copyBody_noRand

/-- Multiplication is exact under the signed-fit condition, with quadratic
cost and linear fresh space. -/
theorem integerTimes_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 2*h+2≤w) (hp : p.HasAt b (integerTimesModule b h)) :
    MeetsContract w p b (integerTimesContract w h) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hm := hasAt_append_left ht
  have hc := hasAt_append_right ht
  change p.HasAt (b+6) _ at hc
  have hmc := multiply_meetsContract hh hw hm
  have hw1 : 1<2^w := lt_of_lt_of_le (by decide : 1<2^1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hw4 : 4<2^w := lt_of_lt_of_le (by decide : 4<2^3)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hcc := copy_meetsContract (h:=h) hw1 hc
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a,d,L,heap,rfl,ha,hd,hva,hvd,hfit⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+7*L<2^w at hbound
  have haw : a<2^w := hwords a (by simp)
  have hdw : d<2^w := hwords d (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  apply runs_start_le
  unfold integerTimesBody
  refine runs_seq_call_le hmc (vs:=[a,d,L,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,rfl,ha,hd,hva,hvd⟩,hz,by change heap+6*L<2^w; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨he₁,hl₁,hh₁,fr₁,hz₁,hv₁,hval₁⟩
    change v₁=heap+6*L at he₁
    change (∀ z<heap,mem₁ z=mem z) at fr₁
    change Valid mem₁ (heap+4*L) h (2*L) at hv₁
    change intVal mem₁ (heap+4*L) h (2*L)=intVal mem a h L*intVal mem d h L at hval₁
    have hvlow : Valid mem₁ (heap+4*L) h L := fun i hi => hv₁ i (by omega)
    have hlow : intVal mem₁ (heap+4*L) h L=intVal mem a h L*intVal mem d h L := by
      rw [intVal_prefix_wrap hv₁ (by omega),hval₁,wrap_of_fits hfit]
    have hv₁w : v₁<2^w := by omega
    have h4Lw : 4*L<2^w := by omega
    have hptrw : heap+4*L<2^w := by omega
    refine runs_seq_call_le hcc (vs:=[heap+4*L,L,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,_,_,rfl,by omega,hvlow⟩,hz₁,by change v₁+L<2^w; omega⟩
    · intro v mem₂ pos₂ hp₂
      rcases hp₂ with ⟨he₂,hl₂,hh₂,fr₂,hz₂,hlimbs,hvalid₂,hval₂⟩
      change v=v₁+L at he₂
      change (∀ z<v₁,mem₂ z=mem₁ z) at fr₂
      change Valid mem₂ v₁ h L at hvalid₂
      change intVal mem₂ v₁ h L=intVal mem₁ (heap+4*L) h L at hval₂
      rw [hlow] at hval₂
      have hvw : v<2^w := by omega
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change v=heap+7*L ∧ heap≤v ∧ v≤heap+7*L ∧ (∀ z<heap,mem₂ z=mem z) ∧
          ZeroFrom mem₂ v ∧ Valid mem₂ (heap+6*L) h L ∧
          intVal mem₂ (heap+6*L) h L=intVal mem a h L*intVal mem d h L
        refine ⟨by omega,by omega,by omega,?_,hz₂,?_,?_⟩
        · intro z hz
          rw [fr₂ z (by omega),fr₁ z hz]
        · rwa [← he₁]
        · rwa [← he₁]
      · simp only [integerTimesContract,multiplyContract,copyContract,heapContract,
          List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,
          argsSize_cons,argsSize_nil]
        nlinarith only [sq_nonneg (L:ℤ)]

/-- Integer coefficient multiplication preserves the fixed-point scale. -/
theorem integerTimes_fixVal {mem mem' : ℕ→ℕ} {a d out h L P : ℕ}
    (hv : intVal mem' out h L=intVal mem a h L*intVal mem d h L) :
    fixVal mem' out h L P=(intVal mem a h L:ℝ)*fixVal mem d h L P := by
  simp only [fixVal,hv,Int.cast_mul]
  ring

end MinCostFlow.Num.IPM
