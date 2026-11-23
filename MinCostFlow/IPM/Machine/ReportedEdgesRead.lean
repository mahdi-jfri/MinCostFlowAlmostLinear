module

public import MinCostFlow.IPM.Machine.ReportedEdges
import WordRAM.Tactic

/-!
# Reading the next reported edge

The reported-list loop reads a name in Detect's actual order and computes
its offset in the dense fixed-point tables. Prove both operations fit in
words before invoking the per-edge entry. This step preserves memory,
the tape position and every other parent register.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The name lookup and table-offset product have actual deterministic
runs with cost at most twenty, and do not change the caller's memory. -/
theorem reportedEdgesRead_runs {w : ℕ} (p : Program) (parent : State)
    (names i L e : ℕ) (ω : ℕ → Bool)
    (hnames : parent.regs 1=names) (hi : parent.regs 20=i) (hL : parent.regs 7=L)
    (hread : parent.mem (names+i)=e)
    (hslot : names+i<2^w) (_hLw : L<2^w) (he : e<2^w) (hoffset : e*L<2^w) :
    ∃ st cost,Runs w p ω reportedEdgesRead parent .normal st cost ∧
      st=⟨parent.mem,Function.update (Function.update parent.regs 22 e) 23 (e*L),parent.pos⟩ ∧
      cost≤20 := by
  have hn : names<2^w := by omega
  have hiw : i<2^w := by omega
  have hr : parent.mem (names+i)<2^w := by omega
  have hrun : ∃ o st cost,Runs w p ω reportedEdgesRead parent o st cost ∧
      (o=.normal ∧ st=⟨parent.mem,Function.update (Function.update parent.regs 22 e) 23 (e*L),parent.pos⟩) ∧
      cost≤20 := by
    apply runs_start_le
    unfold reportedEdgesRead
    refine runs_seq_assign_le (v:=e) (by eval_expr) ?_
    refine runs_assign_le (v:=e*L) (by eval_expr) ⟨rfl,rfl⟩ ?_
    simp only [Expr.size_load,Expr.size_bin,Expr.size_reg]
    omega
  obtain ⟨o,st,cost,hrun,⟨rfl,hst⟩,hc⟩ := hrun
  exact ⟨st,cost,hrun,hst,hc⟩

end MinCostFlow.IPM.Machine
