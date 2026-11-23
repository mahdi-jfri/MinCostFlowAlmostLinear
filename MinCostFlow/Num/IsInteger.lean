module

public import MinCostFlow.Num.IsZero
public import MinCostFlow.Num.IntegerTestFacts
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Testing whether a fixed-point value is an integer

The precision is a multiple of the limb width. Scan its low limbs for zero, stopping
at the block length if the precision is larger. This read-only test costs at most
`19*L+40` and returns one exactly for integer-valued fixed-point numbers.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a,L,P]`. -/
def isIntegerBody (zeroEntry h : ℕ) : Stmt :=
  .assign 3 (.bin .div (.reg 2) (.const h)) ;;
  .cond (.bin .lt (.reg 3) (.reg 1))
    (.call 4 zeroEntry [.reg 0,.reg 3] ;; .ret (.reg 4))
    (.call 4 zeroEntry [.reg 0,.reg 1] ;; .ret (.reg 4))

/-- Integer test and its zero scan. -/
def isIntegerModule (b h : ℕ) : List Stmt := [isIntegerBody (b+1) h,isZeroBody (b+1)]

/-- Read-only integer test; `fixVal_isInteger_iff` identifies the divisibility test
with existence of an integer equal to the represented real number. -/
def isIntegerContract (w h : ℕ) : Contract where
  pre args mem := ∃ a L P,args=[a,L,P] ∧ h∣P ∧ a+L<2^w ∧ Valid mem a h L
  post args mem v mem' := mem'=mem ∧
    v=if (2:ℤ)^args.getD 2 0∣intVal mem (args.getD 0 0) h (args.getD 1 0) then 1 else 0
  cost args _ := 19*args.getD 1 0+40

/-- Integer testing uses no random statement. -/
theorem isIntegerModule_noRand (b h : ℕ) : ∀ s∈isIntegerModule b h,s.NoRand := by
  intro s hs
  simp only [isIntegerModule,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl
  · simp [isIntegerBody,Stmt.NoRand]
  · exact isZeroBody_noRand _

/-- The integer test meets its read-only contract with linear cost. -/
theorem isInteger_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 1<2^w) (hhw : h<2^w)
    (hp : p.HasAt b (isIntegerModule b h)) : MeetsContract w p b (isIntegerContract w h) := by
  have hz : p.HasAt (b+1) (isZeroModule (b+1)) := by
    intro i hi
    have he : i=0 := by change i<1 at hi; omega
    subst i
    simpa [isIntegerModule,isZeroModule] using hp 1 (by simp [isIntegerModule])
  have hzC := isZero_meetsContract (h:=h) hw hz
  have hentry : p.procs[b]?=some (isIntegerBody (b+1) h) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨a,L,P,rfl,hP,ha,hv⟩
  have haw : a<2^w := hwords a (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPw : P<2^w := hwords P (by simp)
  have hqw : P/h<2^w := lt_of_le_of_lt (Nat.div_le_self _ _) hPw
  have hi := intVal_dvd_scale_iff hh hP hv
  apply runs_start_le
  unfold isIntegerBody
  refine runs_seq_assign_le (v:=P/h) (by eval_expr) ?_
  wram_step
  · have hq : P/h<L := by simpa [startState] using hcond
    refine runs_seq_call_le hzC (vs:=[a,P/h]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨a,P/h,rfl,by omega,fun i hi => hv i (by omega)⟩
    · intro v mem₁ pos₁ hp₁
      rcases hp₁ with ⟨hmem,hvalue⟩
      subst mem₁
      change v=if intVal mem a h (P/h)=0 then 1 else 0 at hvalue
      have hvalid : Valid mem a h (P/h) := fun i hi => hv i (by omega)
      rw [min_eq_left (Nat.le_of_lt hq)] at hi
      have he : (intVal mem a h (P/h)=0) ↔ (2:ℤ)^P∣intVal mem a h L :=
        (intVal_eq_zero_iff hvalid).trans hi.symm
      have hvw : v<2^w := by split_ifs at hvalue <;> omega
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change mem=mem ∧ v=if (2:ℤ)^P∣intVal mem a h L then 1 else 0
        exact ⟨rfl,by simpa only [he] using hvalue⟩
      · simp only [isIntegerContract,isZeroContract,List.getD_cons_zero,List.getD_cons_succ,
          Expr.size_bin,Expr.size_reg,Expr.size_const,argsSize_cons,argsSize_nil]
        omega
  · have hq : ¬ P/h<L := by simpa [startState] using hcond
    refine runs_seq_call_le hzC (vs:=[a,L]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨a,L,rfl,ha,hv⟩
    · intro v mem₁ pos₁ hp₁
      rcases hp₁ with ⟨hmem,hvalue⟩
      subst mem₁
      change v=if intVal mem a h L=0 then 1 else 0 at hvalue
      rw [min_eq_right (show L≤P/h by omega)] at hi
      have he : (intVal mem a h L=0) ↔ (2:ℤ)^P∣intVal mem a h L :=
        (intVal_eq_zero_iff hv).trans hi.symm
      have hvw : v<2^w := by split_ifs at hvalue <;> omega
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change mem=mem ∧ v=if (2:ℤ)^P∣intVal mem a h L then 1 else 0
        exact ⟨rfl,by simpa only [he] using hvalue⟩
      · simp only [isIntegerContract,isZeroContract,List.getD_cons_zero,List.getD_cons_succ,
          Expr.size_bin,Expr.size_reg,Expr.size_const,argsSize_cons,argsSize_nil]
        omega

end MinCostFlow.Num
