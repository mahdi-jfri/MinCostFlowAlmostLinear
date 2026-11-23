module

public import MinCostFlow.IPM.Machine.TargetEpochSetup
import WordRAM.Tactic

/-!
# Stopping before the next epoch's initialization

Residual code zero returns the old feasible flow as a converged
answer. Code two writes failure. Both branches finish at the actual
fresh residual workspace and preserve the old explicit coordinates.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The residual terminal branch returns its exact decision and
the unchanged explicit flow address. -/
theorem targetEpoch_terminal_runs {w startup complete record v source heap : ℕ}
    {p : Program} (st : State) (ω : ℕ → Bool)
    (hrecord : MeetsContract w p record (boundedStatusRecordContract w 2))
    (hv : v=0 ∨ v=2)
    (hsource : st.regs 20=source) (hheap : st.regs 23=heap) (hvalue : st.regs 30=v)
    (hSource : source<2^w) (hThree : 3<2^w) (hspace : heap+2<2^w)
    (hz : ZeroFrom st.mem heap) :
    ∃ out final cost,
      Runs w p ω (targetEpochBranch startup complete record) st (.returned out) final cost ∧
      (boundedStatusRecordContract w 2).post [source,if v=0 then 1 else 0,heap] st.mem out final.mem ∧
      out<2^w ∧ cost≤50 := by
  have hOne : 1<2^w := by omega
  have hHeap : heap<2^w := by omega
  have hsmall : v<3 := by omega
  have htest : (Expr.bin .lt (.reg 30) (.const 3)).eval w st=some 1 :=
    Expr.eval_lt_true (x:=v) (y:=3) (by simp [Expr.eval,hvalue]) (by eval_expr) hsmall hOne
  have hstatus : (Expr.bin .eq (.reg 30) (.const 0)).eval w st=some (if v=0 then 1 else 0) := by
    simpa only [Expr.eval] using Expr.eval_eq_op
      (a:=.reg 30) (b:=.const 0) (st:=st) (w:=w)
      (by simp [Expr.eval,hvalue]) (by eval_expr : (Expr.const 0).eval w st=some 0) hOne
  have hargs : evalArgs w st [.reg 20,.bin .eq (.reg 30) (.const 0),.reg 23]=
      some [source,if v=0 then 1 else 0,heap] := by
    apply evalArgs_cons (by simp [Expr.eval,hsource])
    apply evalArgs_cons hstatus
    apply evalArgs_cons (by simp [Expr.eval,hheap])
    rfl
  have hs : (if v=0 then 1 else 0)≤2 := by split_ifs <;> decide
  have hwords : ∀ z∈[source,if v=0 then 1 else 0,heap],z<2^w := by
    wram_words
  obtain ⟨out,final,c,hret,hout,hw,hcost⟩ := targetEpochReturn_runs st ω (.reg 20)
    (.bin .eq (.reg 30) (.const 0)) (.reg 23) hrecord hargs hwords hs hz hspace
  have hRun : Runs w p ω (targetEpochBranch startup complete record) st (.returned out) final (c+4) := by
    apply runs_cond_iff.mpr
    exact ⟨1,c,htest,by simpa using hret,by change c+4=3+c+1; omega⟩
  have hc : c≤39 := hcost
  exact ⟨out,final,c+4,hRun,hout,hw,by omega⟩

/-- `V`-passing variant of `targetEpoch_terminal_runs` for `targetEpochBranchWithV`. -/
theorem targetEpochWithV_terminal_runs {w startup complete record v source heap : ℕ}
    {p : Program} (st : State) (ω : ℕ → Bool)
    (hrecord : MeetsContract w p record (boundedStatusRecordContract w 2))
    (hv : v=0 ∨ v=2)
    (hsource : st.regs 20=source) (hheap : st.regs 23=heap) (hvalue : st.regs 30=v)
    (hSource : source<2^w) (hThree : 3<2^w) (hspace : heap+2<2^w)
    (hz : ZeroFrom st.mem heap) :
    ∃ out final cost,
      Runs w p ω (targetEpochBranchWithV startup complete record) st (.returned out) final cost ∧
      (boundedStatusRecordContract w 2).post [source,if v=0 then 1 else 0,heap] st.mem out final.mem ∧
      out<2^w ∧ cost≤50 := by
  have hOne : 1<2^w := by omega
  have hHeap : heap<2^w := by omega
  have hsmall : v<3 := by omega
  have htest : (Expr.bin .lt (.reg 30) (.const 3)).eval w st=some 1 :=
    Expr.eval_lt_true (x:=v) (y:=3) (by simp [Expr.eval,hvalue]) (by eval_expr) hsmall hOne
  have hstatus : (Expr.bin .eq (.reg 30) (.const 0)).eval w st=some (if v=0 then 1 else 0) := by
    simpa only [Expr.eval] using Expr.eval_eq_op
      (a:=.reg 30) (b:=.const 0) (st:=st) (w:=w)
      (by simp [Expr.eval,hvalue]) (by eval_expr : (Expr.const 0).eval w st=some 0) hOne
  have hargs : evalArgs w st [.reg 20,.bin .eq (.reg 30) (.const 0),.reg 23]=
      some [source,if v=0 then 1 else 0,heap] := by
    apply evalArgs_cons (by simp [Expr.eval,hsource])
    apply evalArgs_cons hstatus
    apply evalArgs_cons (by simp [Expr.eval,hheap])
    rfl
  have hs : (if v=0 then 1 else 0)≤2 := by split_ifs <;> decide
  have hwords : ∀ z∈[source,if v=0 then 1 else 0,heap],z<2^w := by
    wram_words
  obtain ⟨out,final,c,hret,hout,hw,hcost⟩ := targetEpochReturn_runs st ω (.reg 20)
    (.bin .eq (.reg 30) (.const 0)) (.reg 23) hrecord hargs hwords hs hz hspace
  have hRun : Runs w p ω (targetEpochBranchWithV startup complete record) st (.returned out) final (c+4) := by
    apply runs_cond_iff.mpr
    exact ⟨1,c,htest,by simpa using hret,by change c+4=3+c+1; omega⟩
  have hc : c≤39 := hcost
  exact ⟨out,final,c+4,hRun,hout,hw,by omega⟩

end MinCostFlow.IPM.Machine
