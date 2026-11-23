module

public import MinCostFlow.IPM.Machine.EpochFlowCopy
public import MinCostFlow.IPM.Machine.EpochResidual
import WordRAM.Tactic

/-!
# Preparing the next epoch's immutable base and mutable cache

Algorithm 7 (Chen et al., arXiv:2203.00671v2, page 69) first computes
the current cost residual. On continuation the materialized flow
becomes the immutable base. Copy its words to a fresh mutable flow
array, after the fresh residual scalar and before the next Init.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The arguments are the nine-word residual packet. Return code zero
on convergence, code two on rejection, or a heap greater than two for
a new epoch. The new held residual and mutable flow are at determined
offsets from the old heap. -/
def epochBaseBody (residual copy : ℕ) : Stmt :=
  .call 9 residual [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8] ;;
  .cond (.bin .eq (.reg 9) (.const 1))
    (.assign 10 (.bin .add (.reg 5)
      (.bin .mul (.bin .add (.bin .mul (.const 8) (.reg 2)) (.const 4)) (.reg 4))) ;;
      .call 11 copy [.reg 1,.reg 2,.reg 4,.reg 10] ;;
      .ret (.reg 11))
    (.ret (.reg 9))

/-- The precise endpoint immediately after the residual workspace. -/
def epochResidualEnd (m L heap : ℕ) : ℕ := heap+(8*m+4)*L

/-- Control cost, actual residual arithmetic, and an exact linear
copy of the numerical flow words. -/
def epochBaseCost (m L : ℕ) : ℕ :=
  m*(152*L^2+245*L+400)+244*L+17*(m*L)+760

/-- The input is the exact numerical residual input and fresh space
for the conditional copy. Offsets fit on every branch. -/
def epochBaseContract (w h : ℕ) : Contract where
  pre args mem := ∃ c f m target L heap mn mx quarter,
    args=[c,f,m,target,L,heap,mn,mx,quarter] ∧
    (epochResidualContract w h).pre args mem ∧
    0<L ∧ 8<2^w ∧ epochResidualEnd m L heap+m*L<2^w
  post args mem v final := ∃ code residualMem,
    (epochResidualContract w h).post args mem code residualMem ∧
    if code=1 then
      (epochFlowCopyContract w).post [args.getD 1 0,args.getD 2 0,args.getD 4 0,
        epochResidualEnd (args.getD 2 0) (args.getD 4 0) (args.getD 5 0)] residualMem v final
    else v=code ∧ final=residualMem
  cost args _ := epochBaseCost (args.getD 2 0) (args.getD 4 0)

/-- The residual, branch and copy caller has no rand instruction. -/
theorem epochBaseBody_noRand (residual copy : ℕ) : (epochBaseBody residual copy).NoRand := by
  simp [epochBaseBody,Stmt.NoRand]

/-- The actual guarded base preparation runs with the exact
residual-dependent branch and the declared linear work. -/
theorem epochBase_meetsContract {w h entry residual copy : ℕ} {p : Program}
    (hp : p.procs[entry]?=some (epochBaseBody residual copy))
    (hres : MeetsContract w p residual (epochResidualContract w h))
    (hcopy : MeetsContract w p copy (epochFlowCopyContract w)) :
    MeetsContract w p entry (epochBaseContract w h) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨c,f,m,target,L,heap,mn,mx,quarter,rfl,hRpre,hL,hEight,hspace⟩ := hpre
  let next := epochResidualEnd m L heap
  have hnext : next<2^w := by unfold next; omega
  change heap+(8*m+4)*L<2^w at hnext
  have h8m : 8*m<2^w := by
    have h := Nat.le_mul_of_pos_right (n:=8*m+4) hL
    dsimp only [epochResidualEnd] at hspace
    omega
  have h8m4 : 8*m+4<2^w := by
    have h := Nat.le_mul_of_pos_right (n:=8*m+4) hL
    dsimp only [epochResidualEnd] at hspace
    omega
  have hRsize : (8*m+4)*L<2^w := by
    dsimp only [epochResidualEnd] at hspace
    omega
  have hf : f+m*L≤heap := by
    obtain ⟨c',f',m',target',L',heap',mn',mx',quarter',heq,_,hpre,_⟩ := hRpre
    simp only [List.cons.injEq,and_true] at heq
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
    obtain ⟨⟨_,_,_,_,_,_,heq,_,hfEnd,_⟩,_,_⟩ := hpre
    simp only [List.cons.injEq,and_true] at heq
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
    exact hfEnd
  have hOne : 1<2^w := by omega
  apply runs_start_le
  unfold epochBaseBody
  refine runs_seq_call_le hres (vs:=[c,f,m,target,L,heap,mn,mx,quarter]) (by eval_expr) hwords hRpre ?_
  intro code mem' pos' hout
  have hcode : code≤2 := by
    have hh := hout.2.2
    change code=(if _ then 0 else if _ then 1 else 2) at hh
    split_ifs at hh <;> omega
  have hcodeW : code<2^w := by omega
  by_cases heq : code=1
  · subst code
    refine runs_cond_le (v:=1) (Expr.eval_eq_true (by eval_expr) (by eval_expr) rfl hOne) ?_ ?_
    · intro _
      wram_step
      refine runs_seq_call_le hcopy (vs:=[f,m,L,next]) (by eval_expr) ?_ ?_ ?_
      · intro z hz
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact hwords _ (by simp)
        · exact hwords _ (by simp)
        · exact hwords _ (by simp)
        · exact hnext
      · exact ⟨⟨f,m,L,next,rfl,hf.trans (by unfold next epochResidualEnd; omega),hOne⟩,
          hout.1.2.2.2.2.1,hspace⟩
      · intro v final pos'' hcopyPost
        have hv : v=next+m*L := hcopyPost.2
        have hvW : v<2^w := by omega
        refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
        · refine ⟨1,mem',hout,?_⟩
          rw [ite_eq_left rfl]
          exact hcopyPost
        · simp only [epochFlowCopyContract,heapContract,List.getD_cons_zero,List.getD_cons_succ,
            Expr.size_reg,Expr.size_bin,Expr.size_const,argsSize_cons,argsSize_nil,epochBaseCost,
            epochBaseContract,epochResidualContract]
          omega
    · intro h
      omega
  · refine runs_cond_le (v:=0) (Expr.eval_eq_false (by eval_expr) (by eval_expr) heq hOne) ?_ ?_
    · intro h
      exact (h rfl).elim
    · intro _
      refine runs_ret_le (v:=code) (by eval_expr) ?_ ?_
      · exact ⟨code,mem',hout,ite_eq_right heq ▸ ⟨rfl,rfl⟩⟩
      · simp only [epochBaseContract,epochBaseCost,epochResidualContract,List.getD_cons_zero,List.getD_cons_succ,
          argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_reg,Expr.size_const]
        omega

end MinCostFlow.IPM.Machine
