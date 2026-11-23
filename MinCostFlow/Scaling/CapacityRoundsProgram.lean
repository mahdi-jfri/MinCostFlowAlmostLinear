module

public import MinCostFlow.Scaling.ClogTwoProgram
public import MinCostFlow.Scaling.IterationBounds
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Computing the capacity-scaling round count

The model uses `1+11*clog2(m+1)+clog2(U+1)` rounds. Compute both ceiling
logarithms with the proved integer halving procedure, then form that
integer expression. Memory is unchanged and every operation is counted.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[edgeCount,capacityBound]`. -/
def capacityRoundsBody (log : ℕ) : Stmt :=
  .assign 2 (.bin .add (.reg 0) (.const 1)) ;;
  .assign 3 (.bin .add (.reg 1) (.const 1)) ;;
  .call 4 log [.reg 2] ;;
  .call 5 log [.reg 3] ;;
  .assign 6 (.bin .mul (.const 11) (.reg 4)) ;;
  .ret (.bin .add (.bin .add (.const 1) (.reg 6)) (.reg 5))

/-- The round-count entry shares one ceiling-logarithm procedure. -/
def capacityRoundsModule (b : ℕ) : List Stmt := capacityRoundsBody (b+1) :: clogTwoModule (b+1)

/-- Exact round count with fitting intermediate integer arithmetic. -/
def capacityRoundsContract (w m U : ℕ) : Contract where
  pre args _ := args=[m,U] ∧ m+2<2^w ∧ U+2<2^w ∧ capacityRounds m U<2^w ∧ 11<2^w
  post _ mem ret mem' := ret=capacityRounds m U ∧ mem'=mem
  cost _ _ := 40*Nat.clog 2 (m+1)+40*Nat.clog 2 (U+1)+100

/-- Both round-count and ceiling-logarithm entries are deterministic. -/
theorem capacityRoundsModule_noRand (b : ℕ) : ∀ body ∈ capacityRoundsModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityRoundsBody,Stmt.NoRand,and_self]
  · have he : body=clogTwoBody (b+1) := by simpa only [clogTwoModule,List.mem_singleton] using hb
    subst body
    exact clogTwoBody_noRand _

/-- The machine computes exactly the source's round budget without
changing memory and with logarithmic arithmetic work. -/
theorem capacityRounds_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (capacityRoundsModule b)) (m U : ℕ) :
    MeetsContract w p b (capacityRoundsContract w m U) := by
  have hkM := clogTwo_meetsContract (w := w) (hasAt_tail hp) (m+1)
  have hkU := clogTwo_meetsContract (w := w) (hasAt_tail hp) (U+1)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl,hm,hU,hrounds,hw⟩ := hpre
  have hbudget : 1+11*Nat.clog 2 (m+1)+Nat.clog 2 (U+1)<2^w := hrounds
  have hmLog : Nat.clog 2 (m+1)<2^w := by omega
  have hULog : Nat.clog 2 (U+1)<2^w := by omega
  have hscaled : 11*Nat.clog 2 (m+1)<2^w := by omega
  have hpartial : 1+11*Nat.clog 2 (m+1)<2^w := by omega
  apply runs_start_le
  unfold capacityRoundsBody
  refine runs_seq_assign_le (v := m+1) (by eval_expr) ?_
  refine runs_seq_assign_le (v := U+1) (by eval_expr) ?_
  refine runs_seq_call_le hkM (vs := [m+1]) (by eval_expr) (by wram_words) ⟨rfl,by omega,by omega⟩ ?_
  intro logM memM posM hpostM
  obtain ⟨hmemM,hlogM⟩ := hpostM
  change memM=mem at hmemM
  subst memM
  change logM=Nat.clog 2 (m+1) at hlogM
  subst logM
  refine runs_seq_call_le hkU (vs := [U+1]) (by eval_expr) (by wram_words) ⟨rfl,by omega,by omega⟩ ?_
  intro logU memU posU hpostU
  obtain ⟨hmemU,hlogU⟩ := hpostU
  change memU=mem at hmemU
  subst memU
  change logU=Nat.clog 2 (U+1) at hlogU
  subst logU
  refine runs_seq_assign_le (v := 11*Nat.clog 2 (m+1)) (by eval_expr) ?_
  refine runs_ret_le (v := capacityRounds m U) (by change Expr.eval w _ _=some (1+11*Nat.clog 2 (m+1)+Nat.clog 2 (U+1)); eval_expr)
    ⟨rfl,rfl⟩ ?_
  simp only [capacityRoundsContract,clogTwoContract,argsSize_cons,argsSize_nil,
    Expr.size_bin,Expr.size_reg,Expr.size_const]
  omega

/-- Multiplier three on `[m,U]` jointly covers both logarithms, their
weighted sum, all arguments, and the fixed arithmetic constants. -/
theorem capacityRounds_pre_wordSize (m U : ℕ) :
    (∀ x∈[m,U],x<2^wordSize 3 [m,U]) ∧
      (capacityRoundsContract (wordSize 3 [m,U]) m U).pre [m,U] (fun _ => 0) := by
  let B := [m,U].length+[m,U].foldr max 0+2
  have hbase : max m U+4=B := by
    simp only [B,List.length_cons,List.length_nil,List.foldr_cons,List.foldr_nil,Nat.max_zero]
    omega
  have hB4 : 4≤B := by omega
  have h16 : 16≤B^2 := Nat.pow_le_pow_left hB4 2
  have hp := pow_lt_two_pow_wordSize (by decide : 1≤3) [m,U]
  change B^3<2^wordSize 3 [m,U] at hp
  have hpow : 16*B≤B^3 := by simpa only [←pow_succ] using Nat.mul_le_mul h16 (le_refl B)
  have hmLog : Nat.clog 2 (m+1)≤m+1 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hULog : Nat.clog 2 (U+1)≤U+1 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hbudget : capacityRounds m U≤13*B := by
    change 1+11*Nat.clog 2 (m+1)+Nat.clog 2 (U+1)≤13*B
    have hm : m≤max m U := le_max_left _ _
    have hU : U≤max m U := le_max_right _ _
    omega
  refine ⟨?_,rfl,?_,?_,(hbudget.trans (by omega)).trans_lt hp,?_⟩
  · intro x hx
    exact lt_two_pow_wordSize_of_mem (by decide) hx
  · have hm : m≤max m U := le_max_left _ _
    omega
  · have hU : U≤max m U := le_max_right _ _
    omega
  · omega

end MinCostFlow.Scaling.Machine
