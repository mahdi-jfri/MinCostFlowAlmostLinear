module

public import Mathlib.Data.Nat.Log
public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Ceiling binary logarithm of a word

Replace an integer greater than one by its half rounded up. The number of
steps until reaching one is the least exponent whose power of two covers the
input. The scan is read-only and costs at most sixteen steps per reduction.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Ceiling binary logarithm is at most the input value. -/
theorem ceilingLog_le_value (n : ℕ) : Nat.clog 2 n≤n :=
  Nat.clog_le_of_le_pow (le_of_lt Nat.lt_two_pow_self)

/-- Arguments `[n]`. The extra word bound permits rounding `n/2` upwards. -/
def ceilingLogBody (self : ℕ) : Stmt :=
  .cond (.bin .lt (.const 1) (.reg 0))
    (.call 1 self [.bin .div (.bin .add (.reg 0) (.const 1)) (.const 2)] ;;
      .ret (.bin .add (.reg 1) (.const 1)))
    (.ret (.const 0))

/-- A recursively linked ceiling-logarithm body. -/
def ceilingLogModule (b : ℕ) : List Stmt := [ceilingLogBody b]

/-- Exact, read-only ceiling logarithm with its explicit cost. -/
def ceilingLogContract (w : ℕ) : Contract where
  pre args _ := ∃ n,args=[n] ∧ n+1<2^w
  post args mem v mem' := mem'=mem ∧ v=Nat.clog 2 (args.getD 0 0)
  cost args _ := 16*Nat.clog 2 (args.getD 0 0)+6

/-- Ceiling logarithm uses no random statement. -/
theorem ceilingLogModule_noRand (b : ℕ) : ∀ s∈ceilingLogModule b,s.NoRand := by
  intro s hs
  have he : s=ceilingLogBody b := by simpa [ceilingLogModule] using hs
  subst s
  simp [ceilingLogBody,Stmt.NoRand]

/-- The rounded-halving scan computes the least covering exponent for every
input satisfying its extra addition bound. -/
theorem ceilingLog_meetsContract {w b : ℕ} {p : Program} (hw : 2<2^w)
    (hp : p.HasAt b (ceilingLogModule b)) : MeetsContract w p b (ceilingLogContract w) := by
  apply meetsContract_of_rec (fun args _ => args.getD 0 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨n,rfl,hnpw⟩
  change n=k at hk
  subst k
  have hnw : n<2^w := hwords n (by simp)
  have hquotw : (n+1)/2<2^w := lt_of_le_of_lt (Nat.div_le_self _ _) hnpw
  have hlog := ceilingLog_le_value n
  apply runs_start_le
  unfold ceilingLogBody
  wram_step
  · have hn : 1<n := by simpa [startState] using hcond
    have hstep : Nat.clog 2 n=Nat.clog 2 ((n+1)/2)+1 := by
      simpa only [show n+2-1=n+1 by omega] using Nat.clog_of_one_lt (by decide : 1<2) hn
    have hrec : MeetsContract w p b
        ((ceilingLogContract w).below (fun args _ => args.getD 0 0) n) := ih
    refine runs_seq_call_le hrec (vs:=[(n+1)/2]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,rfl,by omega⟩,by change (n+1)/2<n; omega⟩
    · intro v mem' pos' hpost
      rcases hpost with ⟨hmem,hv⟩
      change mem'=mem at hmem
      subst mem'
      change v=Nat.clog 2 ((n+1)/2) at hv
      have hvw : v<2^w := by omega
      have hvpw : v+1<2^w := by omega
      refine runs_ret_le (v:=v+1) (by eval_expr) ?_ ?_
      · exact ⟨rfl,by change v+1=Nat.clog 2 n; omega⟩
      · simp only [ceilingLogContract,Contract.below,List.getD_cons_zero,
          Expr.size_reg,Expr.size_bin,Expr.size_const,argsSize_cons,argsSize_nil]
        omega
  · have hn : ¬1<n := by simpa [startState] using hcond
    refine runs_ret_le (v:=0) (by eval_expr) ?_ ?_
    · have he : Nat.clog 2 n=0 := Nat.clog_of_right_le_one (show n≤1 by omega) 2
      exact ⟨rfl,he.symm⟩
    · simp only [ceilingLogContract,List.getD_cons_zero,Expr.size_reg,Expr.size_bin,Expr.size_const]
      omega

end MinCostFlow.Num.IPM
