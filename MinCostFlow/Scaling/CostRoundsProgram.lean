module

public import MinCostFlow.Scaling.ClogTwoProgram
public import MinCostFlow.Scaling.IterationBounds
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry
import WordRAM.LinkDefs

/-!
# Computing the cost-scaling round count

The model uses `1+clog2(C+1)+clog2(n+1)` rounds. Compute both ceiling
logarithms with the proved integer halving procedure, then form that
integer expression. Memory is unchanged and every operation is counted.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[vertexCount,costBound]`. -/
def costRoundsBody (log : ℕ) : Stmt :=
  .assign 2 (.bin .add (.reg 0) (.const 1)) ;;
  .assign 3 (.bin .add (.reg 1) (.const 1)) ;;
  .call 4 log [.reg 2] ;;
  .call 5 log [.reg 3] ;;
  .ret (.bin .add (.bin .add (.const 1) (.reg 5)) (.reg 4))

/-- The round-count entry shares one ceiling-logarithm procedure. -/
def costRoundsModule (b : ℕ) : List Stmt := costRoundsBody (b+1) :: clogTwoModule (b+1)

/-- Exact round count with fitting intermediate integer arithmetic. -/
def costRoundsContract (w n C : ℕ) : Contract where
  pre args _ := args=[n,C] ∧ n+2<2^w ∧ C+2<2^w ∧ costRounds n C<2^w ∧ 2<2^w
  post _ mem ret mem' := ret=costRounds n C ∧ mem'=mem
  cost _ _ := 40*Nat.clog 2 (n+1)+40*Nat.clog 2 (C+1)+100

/-- Both round-count and ceiling-logarithm entries are deterministic. -/
theorem costRoundsModule_noRand (b : ℕ) : ∀ body ∈ costRoundsModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [costRoundsBody,Stmt.NoRand,and_self]
  · have he : body=clogTwoBody (b+1) := by simpa only [clogTwoModule,List.mem_singleton] using hb
    subst body
    exact clogTwoBody_noRand _

/-- The machine computes exactly the source's round budget without
changing memory and with logarithmic arithmetic work. -/
theorem costRounds_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (costRoundsModule b)) (n C : ℕ) :
    MeetsContract w p b (costRoundsContract w n C) := by
  have hkM := clogTwo_meetsContract (w := w) (hasAt_tail hp) (n+1)
  have hkU := clogTwo_meetsContract (w := w) (hasAt_tail hp) (C+1)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl,hm,hU,hrounds,hw⟩ := hpre
  have hbudget : 1+Nat.clog 2 (C+1)+Nat.clog 2 (n+1)<2^w := hrounds
  have hmLog : Nat.clog 2 (n+1)<2^w := by omega
  have hULog : Nat.clog 2 (C+1)<2^w := by omega
  have hpartial : 1+Nat.clog 2 (C+1)<2^w := by omega
  apply runs_start_le
  unfold costRoundsBody
  refine runs_seq_assign_le (v := n+1) (by eval_expr) ?_
  refine runs_seq_assign_le (v := C+1) (by eval_expr) ?_
  refine runs_seq_call_le hkM (vs := [n+1]) (by eval_expr) (by wram_words) ⟨rfl,by omega,by omega⟩ ?_
  intro logM memM posM hpostM
  obtain ⟨hmemM,hlogM⟩ := hpostM
  change memM=mem at hmemM
  subst memM
  change logM=Nat.clog 2 (n+1) at hlogM
  subst logM
  refine runs_seq_call_le hkU (vs := [C+1]) (by eval_expr) (by wram_words) ⟨rfl,by omega,by omega⟩ ?_
  intro logU memU posU hpostU
  obtain ⟨hmemU,hlogU⟩ := hpostU
  change memU=mem at hmemU
  subst memU
  change logU=Nat.clog 2 (C+1) at hlogU
  subst logU
  refine runs_ret_le (v := costRounds n C) (by change Expr.eval w _ _=some (1+Nat.clog 2 (C+1)+Nat.clog 2 (n+1)); eval_expr)
    ⟨rfl,rfl⟩ ?_
  simp only [costRoundsContract,clogTwoContract,argsSize_cons,argsSize_nil,
    Expr.size_bin,Expr.size_reg,Expr.size_const]
  omega

/-- Multiplier three on `[n,C]` jointly covers both logarithms, their
sum, all arguments, and the fixed arithmetic constants. -/
theorem costRounds_pre_wordSize (n C : ℕ) :
    (∀ x∈[n,C],x<2^wordSize 3 [n,C]) ∧
      (costRoundsContract (wordSize 3 [n,C]) n C).pre [n,C] (fun _ => 0) := by
  let B := [n,C].length+[n,C].foldr max 0+2
  have hbase : max n C+4=B := by
    simp only [B,List.length_cons,List.length_nil,List.foldr_cons,List.foldr_nil,Nat.max_zero]
    omega
  have hB4 : 4≤B := by omega
  have h16 : 16≤B^2 := Nat.pow_le_pow_left hB4 2
  have hp := pow_lt_two_pow_wordSize (by decide : 1≤3) [n,C]
  change B^3<2^wordSize 3 [n,C] at hp
  have hpow : 16*B≤B^3 := by simpa only [←pow_succ] using Nat.mul_le_mul h16 (le_refl B)
  have hmLog : Nat.clog 2 (n+1)≤n+1 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hULog : Nat.clog 2 (C+1)≤C+1 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hbudget : costRounds n C≤13*B := by
    change 1+Nat.clog 2 (C+1)+Nat.clog 2 (n+1)≤13*B
    have hm : n≤max n C := le_max_left _ _
    have hU : C≤max n C := le_max_right _ _
    omega
  refine ⟨?_,rfl,?_,?_,(hbudget.trans (by omega)).trans_lt hp,?_⟩
  · intro x hx
    exact lt_two_pow_wordSize_of_mem (by decide) hx
  · have hm : n≤max n C := le_max_left _ _
    omega
  · have hU : C≤max n C := le_max_right _ _
    omega
  · omega

end MinCostFlow.Scaling.Machine
