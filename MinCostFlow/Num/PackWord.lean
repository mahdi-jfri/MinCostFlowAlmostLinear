module

public import MinCostFlow.Num.Representation
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Packing a small unsigned magnitude into one word

Read the high limbs recursively, multiply by the base, and add the current limb.
Every partial value is bounded by the full value, so a magnitude smaller than one
word can be packed without an overflowing intermediate operation. The scan is read-only.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a,L]`, returning the unsigned value in one word. -/
def packWordBody (self h : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.call 2 self [.bin .add (.reg 0) (.const 1),.bin .sub (.reg 1) (.const 1)] ;;
     .ret (.bin .add (.load (.reg 0)) (.bin .mul (.const (base h)) (.reg 2))))

/-- Unsigned magnitude packing. -/
def packWordModule (b h : ℕ) : List Stmt := [packWordBody b h]

/-- A read-only conversion for an unsigned block whose value fits one word. -/
def packWordContract (w h : ℕ) : Contract where
  pre args mem := ∃ a L,args=[a,L] ∧ a+L<2^w ∧ Valid mem a h L ∧ unsignedVal mem a h L<2^w
  post args mem v mem' := mem'=mem ∧ v=unsignedVal mem (args.getD 0 0) h (args.getD 1 0)
  cost args _ := 25*args.getD 1 0+6

/-- Magnitude packing uses no random statement. -/
theorem packWordBody_noRand (b h : ℕ) : (packWordBody b h).NoRand := by simp [packWordBody,Stmt.NoRand]

/-- Packing a fitting magnitude meets its read-only contract in linear time. -/
theorem packWord_meetsContract {w h b : ℕ} {p : Program}
    (hw : 1<2^w) (hb : base h<2^w) (hp : p.HasAt b (packWordModule b h)) :
    MeetsContract w p b (packWordContract w h) := by
  apply meetsContract_of_rec (fun args _ => args.getD 1 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨a,L,rfl,ha,hv,hu⟩
  change L=k at hk
  subst k
  have haw : a<2^w := hwords a (by simp)
  have hLw : L<2^w := hwords L (by simp)
  apply runs_start_le
  unfold packWordBody
  wram_step
  · have he : L=0 := by simpa [startState] using hcond
    subst L
    refine runs_ret_le (by eval_expr) ?_ ?_
    · exact ⟨rfl,rfl⟩
    · simp only [packWordContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_bin,Expr.size_reg,Expr.size_const]
      omega
  · have he : L≠0 := by simpa [startState] using hcond
    obtain ⟨M,rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
    have hMw : M<2^w := by omega
    obtain ⟨hvlow,hvtail⟩ := valid_succ.mp hv
    have htail : unsignedVal mem (a+1) h M<2^w := by
      have hbpos := base_pos h
      change mem a+base h*unsignedVal mem (a+1) h M<2^w at hu
      nlinarith only [hu,hbpos]
    have hproduct : base h*unsignedVal mem (a+1) h M<2^w := by
      change mem a+base h*unsignedVal mem (a+1) h M<2^w at hu
      omega
    have hloww : mem a<2^w := lt_trans hvlow hb
    refine runs_seq_call_le ih (vs:=[a+1,M]) (by eval_expr; simp [Expr.eval,BinOp.eval,startState,hw,hMw]) (by wram_words) ?_ ?_
    · exact ⟨⟨a+1,M,rfl,by omega,hvtail,htail⟩,by simp only [List.getD_cons_zero,List.getD_cons_succ]; omega⟩
    · intro v mem₁ pos₁ hp₁
      rcases hp₁ with ⟨hmem,hvalue⟩
      subst mem₁
      change v=unsignedVal mem (a+1) h M at hvalue
      have hvw : v<2^w := by omega
      refine runs_ret_le (v:=unsignedVal mem a h (M+1)) (by simp only [unsignedVal]; eval_expr)
        ?_ ?_
      · exact ⟨rfl,rfl⟩
      · simp only [packWordContract,Contract.below,List.getD_cons_zero,List.getD_cons_succ,
          Expr.size_bin,Expr.size_reg,Expr.size_const,Expr.size_load,argsSize_cons,argsSize_nil]
        omega

end MinCostFlow.Num
