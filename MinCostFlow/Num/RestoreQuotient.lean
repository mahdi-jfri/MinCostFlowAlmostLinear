module

public import MinCostFlow.Num.IsZero
public import MinCostFlow.Num.Copy
public import MinCostFlow.Num.NegateCarry
import MinCostFlow.Num.DivisionRestore
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Restoring the quotient sign

Equal input signs need the unsigned quotient copied. Different signs need its negative,
with one extra unit when the remainder is nonzero. A zero test supplies the complement
carry, so both cases take linear time and allocate just the output block.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[quotient,remainder,L,negative,heap]`, with a Boolean negative flag. -/
def restoreQuotientBody (zeroEntry copy neg : ℕ) : Stmt :=
  .cond (.reg 3)
    (.call 5 zeroEntry [.reg 1,.bin .add (.reg 2) (.const 1)] ;;
     .call 6 neg [.reg 0,.reg 2,.reg 5,.reg 4] ;; .ret (.reg 6))
    (.call 6 copy [.reg 0,.reg 2,.reg 4] ;; .ret (.reg 6))

/-- Quotient sign restoration and its three helpers. -/
def restoreQuotientModule (b h : ℕ) : List Stmt :=
  [restoreQuotientBody (b+1) (b+2) (b+3)] ++
    (isZeroModule (b+1) ++ (copyModule (b+2) ++ negateCarryModule (b+3) h))

/-- Mathematical result of restoring a quotient sign. -/
def restoredQuotient (q r negative : ℕ) : ℤ :=
  if negative = 0 then (q : ℤ) else -(q : ℤ) - if r = 0 then 0 else 1

/-- Sign restoration wraps the mathematical quotient if it exceeds the signed range. -/
def restoreQuotientContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ q r L negative heap, args=[q,r,L,negative,heap] ∧
      q+L≤heap ∧ r+(L+1)≤heap ∧ negative≤1 ∧ Valid mem q h L ∧ Valid mem r h (L+1))
    (fun args mem mem' => Valid mem' (heapArg args) h (args.getD 2 0) ∧
      intVal mem' (heapArg args) h (args.getD 2 0) = wrap h (args.getD 2 0)
        (restoredQuotient (unsignedVal mem (args.getD 0 0) h (args.getD 2 0))
          (unsignedVal mem (args.getD 1 0) h (args.getD 2 0+1)) (args.getD 3 0)))
    (fun args _ => 55*args.getD 2 0+80) (fun args _ => args.getD 2 0)
  { C with post := fun args mem v mem' => v=heapArg args+args.getD 2 0 ∧ C.post args mem v mem' }

/-- Sign restoration uses no random statement. -/
theorem restoreQuotientModule_noRand (b h : ℕ) : ∀ s ∈ restoreQuotientModule b h, s.NoRand := by
  intro s hs
  simp only [restoreQuotientModule,List.mem_append,List.mem_singleton,isZeroModule,copyModule,negateCarryModule] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · simp [restoreQuotientBody,Stmt.NoRand]
  · exact isZeroBody_noRand _
  · exact copyBody_noRand
  · exact negateCarryBody_noRand _ _

/-- Sign restoration meets its heap contract with linear cost. -/
theorem restoreQuotient_meetsContract {w h b : ℕ} {p : Program}
    (hw : 1<2^w) (hb : base h<2^w)
    (hp : p.HasAt b (restoreQuotientModule b h)) :
    MeetsContract w p b (restoreQuotientContract w h) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hz := hasAt_append_left ht
  have ht₂ := hasAt_append_right ht
  change p.HasAt (b+2) _ at ht₂
  have hc := hasAt_append_left ht₂
  have hn := hasAt_append_right ht₂
  change p.HasAt (b+3) _ at hn
  have hzero := isZero_meetsContract (h:=h) hw hz
  have hcopy := copy_meetsContract (h:=h) hw hc
  have hneg := negateCarry_meetsContract hw hb hn
  have hentry : p.procs[b]? = some (restoreQuotientBody (b+1) (b+2) (b+3)) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨q,r,L,negative,heap,rfl,hq,hr,hflag,hvq,hvr⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+L<2^w at hbound
  have hqw : q<2^w := hwords q (by simp)
  have hrw : r<2^w := hwords r (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hnw : negative<2^w := hwords negative (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have hMw : L+1<2^w := by omega
  apply runs_start_le
  unfold restoreQuotientBody
  refine runs_cond_le (v:=negative) (by eval_expr) ?_ ?_
  · intro hnonzero
    refine runs_seq_call_le hzero (vs:=[r,L+1]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨r,L+1,rfl,by omega,hvr⟩
    · intro carry mem₁ pos₁ hp₁
      rcases hp₁ with ⟨hmem,hcarry⟩
      subst mem₁
      change carry = if intVal mem r h (L+1)=0 then 1 else 0 at hcarry
      have hce : carry = if unsignedVal mem r h (L+1)=0 then 1 else 0 := by
        simpa only [intVal_eq_zero_iff hvr] using hcarry
      have hc : carry≤1 := by split_ifs at hcarry <;> omega
      have hcw : carry<2^w := by omega
      refine runs_seq_call_le hneg (vs:=[q,L,carry,heap]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨q,L,carry,heap,rfl,hq,hc,hvq⟩,hz,hbound⟩
      · intro v mem₂ pos₂ hp₂
        rcases hp₂ with ⟨hv,hlo,hhi,hframe,hz₂,hlist⟩
        change v=heap+L at hv
        change (∀ z<heap,mem₂ z=mem z) at hframe
        change ListAt mem₂ heap (digits h L (capacity h L-1-unsignedVal mem q h L+carry)) at hlist
        obtain ⟨hvalid,hvalue⟩ := negateCarry_unsigned_value hvq hc hlist
        have he : -(unsignedVal mem q h L : ℤ)-1+(carry:ℤ) =
            restoredQuotient (unsignedVal mem q h L) (unsignedVal mem r h (L+1)) negative := by
          unfold restoredQuotient
          rw [ite_eq_right hnonzero,hce]
          split_ifs <;> norm_num
        rw [he] at hvalue
        have hvw : v<2^w := by omega
        refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
        · exact ⟨hv,hlo,hhi,hframe,hz₂,hvalid,hvalue⟩
        · simp only [restoreQuotientContract,isZeroContract,negateCarryContract,heapContract,
            List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,
            argsSize_cons,argsSize_nil]
          omega
  · intro hflagzero
    refine runs_seq_call_le hcopy (vs:=[q,L,heap]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨q,L,heap,rfl,hq,hvq⟩,hz,hbound⟩
    · intro v mem₁ pos₁ hp₁
      rcases hp₁ with ⟨hv,hlo,hhi,hframe,hz₁,hlimbs,hvalid,hvalue⟩
      change v=heap+L at hv
      change intVal mem₁ heap h L=intVal mem q h L at hvalue
      have he : intVal mem q h L = wrap h L
          (restoredQuotient (unsignedVal mem q h L) (unsignedVal mem r h (L+1)) negative) := by
        rw [restoredQuotient,ite_eq_left hflagzero,wrap_natCast,Nat.mod_eq_of_lt (unsignedVal_lt hvq)]
        rfl
      have hvw : v<2^w := by omega
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · exact ⟨hv,hlo,hhi,hframe,hz₁,hvalid,hvalue.trans he⟩
      · simp only [restoreQuotientContract,copyContract,heapContract,List.getD_cons_zero,
          List.getD_cons_succ,Expr.size_reg,argsSize_cons,argsSize_nil]
        omega

end MinCostFlow.Num
