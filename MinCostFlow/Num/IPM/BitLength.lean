module

public import Mathlib.Data.Nat.Size
public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Bit length of a word

Repeated division by two counts the binary digits, including zero digits
between the highest and lowest set bits. Zero has length zero. The procedure
preserves all memory and uses at most fourteen steps per binary digit.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- A positive word loses exactly one binary digit on division by two. -/
theorem size_div_two_step {n : ℕ} (hn : 0<n) : n.size=(n/2).size+1 := by
  have he (k : ℕ) : n.size≤k+1 ↔ (n/2).size≤k := by
    rw [Nat.size_le,Nat.size_le,pow_succ]
    omega
  have hupper : n.size≤(n/2).size+1 := (he _).mpr le_rfl
  have hpos := Nat.size_pos.mpr hn
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hlower : (n/2).size≤k := (he k).mp (by omega)
  omega

/-- Binary length is at most the word's natural value. -/
theorem size_le_value (n : ℕ) : n.size≤n := Nat.size_le.mpr Nat.lt_two_pow_self

/-- Arguments `[n]`. -/
def bitLengthBody (self : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 0) (.const 0)) (.ret (.const 0))
    (.call 1 self [.bin .div (.reg 0) (.const 2)] ;;
      .ret (.bin .add (.reg 1) (.const 1)))

/-- A single recursively linked bit-length body. -/
def bitLengthModule (b : ℕ) : List Stmt := [bitLengthBody b]

/-- Read-only exact binary length with explicit linear cost in the digit count. -/
def bitLengthContract : Contract where
  pre args _ := ∃ n,args=[n]
  post args mem v mem' := mem'=mem ∧ v=(args.getD 0 0).size
  cost args _ := 14*(args.getD 0 0).size+6

/-- Bit length uses no randomness. -/
theorem bitLengthModule_noRand (b : ℕ) : ∀ s∈bitLengthModule b,s.NoRand := by
  intro s hs
  have he : s=bitLengthBody b := by simpa [bitLengthModule] using hs
  subst s
  simp [bitLengthBody,Stmt.NoRand]

/-- The binary scan computes `Nat.size` for every word, without changing memory. -/
theorem bitLength_meetsContract {w b : ℕ} {p : Program} (hw : 2<2^w)
    (hp : p.HasAt b (bitLengthModule b)) : MeetsContract w p b bitLengthContract := by
  apply meetsContract_of_rec (fun args _ => args.getD 0 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨n,rfl⟩
  change n=k at hk
  subst k
  have hnw : n<2^w := hwords n (by simp)
  have hquotw : n/2<2^w := lt_of_le_of_lt (Nat.div_le_self _ _) hnw
  have hsize := size_le_value n
  apply runs_start_le
  unfold bitLengthBody
  wram_step
  · have hn0 : n=0 := by simpa [startState] using hcond
    subst n
    refine runs_ret_le (v:=0) (by eval_expr) ?_ ?_
    · exact ⟨rfl,rfl⟩
    · simp [bitLengthContract,Expr.size_bin,Expr.size_reg,Expr.size_const]
  · have hn0 : n≠0 := by simpa [startState] using hcond
    have hn : 0<n := Nat.pos_of_ne_zero hn0
    have hstep := size_div_two_step hn
    have hrec : MeetsContract w p b (bitLengthContract.below (fun args _ => args.getD 0 0) n) := ih
    refine runs_seq_call_le hrec (vs:=[n/2]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨_,rfl⟩,by change n/2<n; exact Nat.div_lt_self hn (by decide)⟩
    · intro v mem' pos' hpost
      rcases hpost with ⟨hmem,hv⟩
      change mem'=mem at hmem
      subst mem'
      change v=(n/2).size at hv
      have hvw : v<2^w := by omega
      have hvpw : v+1<2^w := by omega
      refine runs_ret_le (v:=v+1) (by eval_expr) ?_ ?_
      · exact ⟨rfl,by change v+1=n.size; omega⟩
      · simp only [bitLengthContract,Contract.below,List.getD_cons_zero,
          Expr.size_reg,Expr.size_bin,Expr.size_const,argsSize_cons,argsSize_nil]
        omega

end MinCostFlow.Num.IPM
