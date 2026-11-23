module

public import MinCostFlow.IPM.Machine.TargetSearchParameters
public import MinCostFlow.IPM.Machine.TargetSearchProgram
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Word computations for the first bisection call

The signed targets use an unsigned offset from (mU^2). The
two verified loop-limit routines compute the bounded stage count
and the bisection count. This entry stores both beside the radius.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[m,U,k,j,heap]`. Output is `[limit,radius,rounds]`. -/
def solverLimitsBody (bits limit rounds : ℕ) : Stmt :=
  .call 5 bits [.reg 0] ;;
  .call 6 bits [.reg 1] ;;
  .call 7 limit [.bin .add (.reg 5) (.reg 6),.reg 2,.reg 3] ;;
  .assign 8 (.bin .mul (.reg 0) (.bin .mul (.reg 1) (.reg 1))) ;;
  .call 9 rounds [.reg 8] ;;
  .store (.reg 4) (.reg 7) ;;
  .store (.bin .add (.reg 4) (.const 1)) (.reg 8) ;;
  .store (.bin .add (.reg 4) (.const 2)) (.reg 9) ;;
  .ret (.bin .add (.reg 4) (.const 3))

/-- Exact three-word read-only configuration for repeated tests. -/
def solverLimitWords (m U k : ℕ) : List ℕ :=
  [targetTestLimit m U k,m*U^2,targetSearchRounds (m*U^2)]

/-- Limits take constant workspace, with linear cost in the relevant bit lengths. -/
def solverLimitsContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ m U k h,args=[m,U,k,Num.IPM.alphaExponent m U,h] ∧
      2≤m*U ∧ 2*(m*U^2)<2^w ∧ targetTestLimit m U k<2^w ∧ m.size+U.size<2^w)
    (fun args _ mem' => ListAt mem' (heapArg args) (solverLimitWords (args.getD 0 0)
      (args.getD 1 0) (args.getD 2 0)))
    (fun args _ => 14*((args.getD 0 0).size+(args.getD 1 0).size+
      targetSearchRounds ((args.getD 0 0)*(args.getD 1 0)^2))+550)
    (fun _ _ => 3)
  {C with post := fun args mem endPtr mem' => C.post args mem endPtr mem' ∧ endPtr=heapArg args+3}

/-- The limit computations use deterministic scans and word arithmetic. -/
theorem solverLimitsBody_noRand (bits limit rounds : ℕ) : (solverLimitsBody bits limit rounds).NoRand := by
  simp [solverLimitsBody,Stmt.NoRand]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 300000 in
/-- Read the two sizes, calculate the exact search radius and bounds,
and write all three words using only fresh memory. -/
theorem solverLimits_meetsContract {w entry bits limit rounds : ℕ} {p : Program}
    (hbody : p.procs[entry]?=some (solverLimitsBody bits limit rounds))
    (hBits : MeetsContract w p bits Num.IPM.bitLengthContract)
    (hLimit : MeetsContract w p limit (targetTestLimitContract w))
    (hRounds : MeetsContract w p rounds (targetSearchRoundsContract w)) :
    MeetsContract w p entry (solverLimitsContract w) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hword hpre
  obtain ⟨⟨m,U,k,h,rfl,hsize,hspan,hlimit,hbits⟩,hzero,hspace⟩ := hpre
  let j := Num.IPM.alphaExponent m U
  let l := targetTestLimit m U k
  let b := m*U^2
  let r := targetSearchRounds b
  change h+3<2^w at hspace
  change ZeroFrom mem h at hzero
  have hm : 0 < m := by
    by_contra hn
    have he : m=0 := by omega
    simp [he] at hsize
  have hU : U*U<2^w := by
    rw [←pow_two]
    exact (Nat.le_mul_of_pos_left _ hm).trans_lt (show b<2^w by omega)
  have hb : b<2^w := by omega
  have hmW : m<2^w := hword _ (by simp)
  have hUW : U<2^w := hword _ (by simp)
  have hkW : k<2^w := hword _ (by simp)
  have hjW : j<2^w := hword _ (by simp [j])
  have hlW : l<2^w := hlimit
  have hrW : r<2^w := ((Nat.size_le).mpr hspan).trans_lt (Nat.lt_two_pow_self (n := w))
  have hhW : h<2^w := by omega
  have hh1 : h+1<2^w := by omega
  have hh2 : h+2<2^w := by omega
  have hOne : 1<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hThree : 3<2^w := by omega
  apply runs_start_le
  unfold solverLimitsBody
  refine runs_seq_call_le hBits (vs:=[m]) (by eval_expr) (by wram_words) ⟨m,rfl⟩ ?_
  intro x mem₁ pos₁ h₁
  change mem₁=mem ∧ x=m.size at h₁
  obtain ⟨h₁mem,h₁x⟩ := h₁
  subst mem₁ x
  refine runs_seq_call_le hBits (vs:=[U]) (by eval_expr) (by wram_words) ⟨U,rfl⟩ ?_
  intro y mem₂ pos₂ h₂
  change mem₂=mem ∧ y=U.size at h₂
  obtain ⟨h₂mem,h₂y⟩ := h₂
  subst mem₂ y
  refine runs_seq_call_le hLimit (vs:=[m.size+U.size,k,j])
    (evalArgs_cons (Expr.eval_add rfl rfl hbits) rfl) (by wram_words)
    ⟨m,U,k,rfl,hsize,hlimit⟩ ?_
  intro v mem₃ pos₃ h₃
  change mem₃=mem ∧ v=l at h₃
  obtain ⟨h₃mem,h₃v⟩ := h₃
  subst mem₃ v
  refine runs_seq_assign_le (v:=b) (by
    change _=some (m*U^2)
    rw [pow_two]
    have hb' : m*(U*U)<2^w := by simpa only [b,pow_two] using hb
    eval_expr) ?_
  refine runs_seq_call_le hRounds (vs:=[b]) (by eval_expr) (by wram_words) ⟨b,rfl,hspan⟩ ?_
  intro q mem₄ pos₄ h₄
  change mem₄=mem ∧ q=r at h₄
  obtain ⟨h₄mem,h₄q⟩ := h₄
  subst mem₄ q
  refine runs_seq_store_le (x:=h) (v:=l) rfl rfl ?_
  refine runs_seq_store_le (x:=h+1) (v:=b) (Expr.eval_add rfl (Expr.eval_const hOne) hh1) rfl ?_
  refine runs_seq_store_le (x:=h+2) (v:=r) (Expr.eval_add rfl (Expr.eval_const hTwo) hh2) rfl ?_
  refine runs_ret_le (v:=h+3) (Expr.eval_add rfl (Expr.eval_const hThree) hspace) ?_ ?_
  · let final := Function.update (Function.update (Function.update mem h l) (h+1) b) (h+2) r
    have hf : ∀ x<h,final x=mem x := by
      intro x hx
      simp only [final,Function.update_of_ne (show x≠h+2 by omega),
        Function.update_of_ne (show x≠h+1 by omega),Function.update_of_ne (show x≠h by omega)]
    have hz : ZeroFrom final (h+3) := by
      intro x hx
      simp only [final,Function.update_of_ne (show x≠h+2 by omega),
        Function.update_of_ne (show x≠h+1 by omega),Function.update_of_ne (show x≠h by omega)]
      exact hzero x (by omega)
    have ht : ListAt final h (solverLimitWords m U k) := by
      intro x hx
      change x<3 at hx
      interval_cases x <;> simp [solverLimitWords,final,l,b,r,Function.update_of_ne]
    exact ⟨⟨show h≤h+3 by omega,show h+3≤h+3 from le_rfl,hf,hz,ht⟩,rfl⟩
  · simp only [solverLimitsContract,heapContract,Num.IPM.bitLengthContract,
      targetTestLimitContract,targetSearchRoundsContract,argsSize_cons,argsSize_nil,
      Expr.size_reg,Expr.size_const,Expr.size_bin,List.getD_cons_succ,List.getD_cons_zero]
    dsimp only [r,b]
    omega

end MinCostFlow.IPM.Machine
