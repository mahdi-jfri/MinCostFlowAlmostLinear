module

public import WordRAM.Contract
public import Mathlib.Data.Nat.Log
import WordRAM.Logic
import WordRAM.Tactic

/-!
# Computing the ceiling binary logarithm

The sorting and bottleneck models use `Nat.clog 2 n` as a finite iteration
budget. For `n` above one, recursively take the ceiling half and add one.
Mathlib's ceiling-log recurrence identifies the result. All intermediate
numbers are at most `n+1`, and memory is unchanged.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Argument `[n]`. -/
def clogTwoBody (self : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 0) (.const 2)) (.ret (.const 0))
    (.call 1 self [.bin .div (.bin .add (.reg 0) (.const 1)) (.const 2)] ;;
     .ret (.bin .add (.reg 1) (.const 1)))

/-- A single recursive ceiling-log procedure. -/
def clogTwoModule (b : ℕ) : List Stmt := [clogTwoBody b]

/-- The input's successor fits, and the result is exactly its ceiling binary
logarithm with logarithmic cost and no memory changes. -/
def clogTwoContract (w n : ℕ) : Contract where
  pre args _ := args = [n] ∧ n+1 < 2^w ∧ 2 < 2^w
  post _ mem ret mem' := mem'=mem ∧ ret=Nat.clog 2 n
  cost _ _ := 40*Nat.clog 2 n+20

/-- Ceiling-log computation has no random instruction. -/
theorem clogTwoBody_noRand (b : ℕ) : (clogTwoBody b).NoRand := by
  simp only [clogTwoBody,Stmt.NoRand,and_self]

private theorem clogTwo_half (n : ℕ) (hn : 1 < n) :
    Nat.clog 2 n=Nat.clog 2 ((n+1)/2)+1 := by
  have h := Nat.clog_of_one_lt (by decide : 1 < 2) hn
  have heq : n+2-1=n+1 := by omega
  simpa only [heq] using h

/-- The procedure computes the exact iteration budget used by sorting and
search, following the standard ceiling-half recurrence. -/
theorem clogTwo_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (clogTwoModule b)) (n : ℕ) :
    MeetsContract w p b (clogTwoContract w n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨rfl,hs,htwo⟩ := hpre
    have hnword : n < 2^w := by omega
    have hone : 1 < 2^w := by omega
    have hlog : Nat.clog 2 n ≤ n :=
      Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
    apply runs_start_le
    unfold clogTwoBody
    wram_step
    · have hn : n ≤ 1 := by
        have hh : n < 2 := by simpa only [startState,List.getD_cons_zero] using hcond
        omega
      refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
      · exact ⟨rfl,by rw [Nat.clog_of_right_le_one hn]; rfl⟩
      · simp only [clogTwoContract,Nat.clog_of_right_le_one hn,
          Expr.size_bin,Expr.size_reg,Expr.size_const]
        omega
    · have hn : 1 < n := by
        have hh : ¬ n < 2 := by simpa only [startState,List.getD_cons_zero] using hcond
        omega
      have hhalf : (n+1)/2 < n := by omega
      have hhalfword : (n+1)/2 < 2^w := by omega
      have hhalfSucc : (n+1)/2+1 < 2^w := by omega
      have heq := clogTwo_half n hn
      have hreturn : Nat.clog 2 ((n+1)/2)+1 < 2^w := by omega
      have hk := ih ((n+1)/2) hhalf
      refine runs_seq_call_le hk (vs := [(n+1)/2]) (by eval_expr) (by wram_words)
        ⟨rfl,hhalfSucc,htwo⟩ ?_
      intro ret memR posR hpostR
      obtain ⟨hmem,hret⟩ := hpostR
      subst memR
      subst ret
      refine runs_ret_le (v := Nat.clog 2 ((n+1)/2)+1) (by eval_expr) ?_ ?_
      · exact ⟨rfl,heq.symm⟩
      · simp only [clogTwoContract,argsSize_cons,argsSize_nil,
          Expr.size_bin,Expr.size_reg,Expr.size_const]
        rw [heq]
        omega

/-- Every natural input has simultaneous successor and constant bounds at
one finite word size. -/
theorem exists_clogTwo_pre (n : ℕ) :
    ∃ w,(∀ x ∈ [n],x < 2^w) ∧ (clogTwoContract w n).pre [n] (fun _ => 0) := by
  let w := n+5
  have hw : n+5 < 2^w := Nat.lt_two_pow_self
  refine ⟨w,?_,rfl,by omega,by omega⟩
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  subst x
  omega

end MinCostFlow.Scaling.Machine
