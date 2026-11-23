module

public import MinCostFlow.Scaling.ExtractCycleContract
import MinCostFlow.Scaling.CycleRunProgram
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Executing complete cycle extraction

Compose initialization with the proved bounded traversal at fuel
`6*m+1`. The initial potential supplies the traversal word bound. Fresh
allocation and the preserved source prefix supply its other premises.
The resulting state is exactly the extraction model's state.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Cycle extraction computes the exact model state at cost at most
`7600*m+2000`, preserving the whole source graph and flow prefix. -/
theorem extractCycle_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (extractCycleModule b)) (J : Circulation) (flow : Fin J.m → ℤ) (C : ℕ) :
    MeetsContract w p b (extractCycleContract w J flow C) := by
  have ht := hasAt_tail hp
  have hkI := cycleInitial_meetsContract (w := w) (hasAt_append_left ht) J flow
  have hkR := cycleRun_meetsContract (w := w) (hasAt_append_right ht) J (J.cycleInitial flow) 0 C (6*J.m+1)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,flowPtr,base,rfl,hgraph,hflow,hgraphEnd,hflowEnd,hvalues,hcosts,hzero,hspace,hbudget,hw⟩ := hpre
  have ha : a<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hb : base<2^w := by omega
  have hm : J.m<2^w := by omega
  have h6m : 6*J.m<2^w := by omega
  have hfuel : 6*J.m+1<2^w := by omega
  apply runs_start_le
  unfold extractCycleBody
  refine runs_seq_call_le hkI (vs := [a,flowPtr,base]) (by eval_expr) hwords
    ⟨a,flowPtr,base,rfl,hgraph,hflow,hgraphEnd,hflowEnd,hvalues,hzero,by omega,hw⟩ ?_
  intro initHeap memI posI hpostI
  obtain ⟨hlo,hhi,hstateI,hzI,hframeI,hheaderI⟩ := hpostI
  change cycleNodes J.n base≤ initHeap at hlo
  change initHeap≤cycleNodes J.n base+4*J.m at hhi
  change CycleStateAt memI base initHeap (J.cycleInitial flow) at hstateI
  change ZeroFrom memI initHeap at hzI
  change (∀ x<base,memI x=mem x) at hframeI
  change (∀ i<9,memI (base+i)<2^w) at hheaderI
  have hnodesNum : base+10+3*J.n≤ initHeap := hlo
  have hhiNum : initHeap≤base+10+3*J.n+4*J.m := hhi
  have hiWord : initHeap<2^w := by omega
  have hgraphI : ListAt memI a J.solverWords :=
    hgraph.of_agree_below (h₀ := base) hgraphEnd hframeI
  have hmCell := (solver_header_at J hgraphI).2
  have hpotential := J.cycleInitial_potential flow
  have hpotentialWord : (J.cycleInitial flow).potential+1<2^w := by omega
  have hbudgetRun : 0+(6*J.m+1+1)*C<2^w := by simpa only [Nat.zero_add,Nat.add_assoc,Nat.reduceAdd] using hbudget
  have hspaceRun : initHeap+4*(6*J.m+1)+4<2^w := by omega
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 6*J.m+1) (by eval_expr) ?_
  refine runs_seq_call_le hkR (vs := [a,base,6*J.m+1,initHeap]) (by eval_expr) (by wram_words)
    ⟨a,base,initHeap,rfl,hgraphI,hgraphEnd,hstateI,hlo,hheaderI,
      by change (0 : ℤ).natAbs≤0; exact le_rfl,hcosts,hbudgetRun,hpotentialWord,hzI,hspaceRun,hfuel,hw⟩ ?_
  intro ret memR posR hpostR
  obtain ⟨hloR,hhiR,hstateR,hzR,hframeR,hheaderR⟩ := hpostR
  change initHeap≤ret at hloR
  change ret≤ initHeap+4*(6*J.m+1) at hhiR
  change (∀ x< initHeap,x<base ∨ cycleNodes J.n base≤x → memR x=memI x) at hframeR
  refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change cycleNodes J.n base≤ret ∧ ret≤cycleNodes J.n base+28*J.m+4 ∧
      CycleStateAt memR base ret (J.extractCycleModel flow).1 ∧ ZeroFrom memR ret ∧
      (∀ x<base,memR x=mem x) ∧ ∀ i<9,memR (base+i)<2^w
    refine ⟨hlo.trans hloR,by omega,hstateR,hzR,?_,hheaderR⟩
    intro x hx
    exact (hframeR x (by omega) (Or.inl hx)).trans (hframeI x hx)
  · simp only [extractCycleContract,cycleInitialContract,cycleRunContract,argsSize_cons,argsSize_nil,
      Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
    omega

/-- The explicit extraction cost is linear in the graph size. -/
theorem extractCycle_cost_le (w : ℕ) (J : Circulation) (flow : Fin J.m → ℤ) (C : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) :
    (extractCycleContract w J flow C).cost args mem≤9600*(J.m+J.n+1) := by
  change 7600*J.m+2000≤9600*(J.m+J.n+1)
  omega

end MinCostFlow.Scaling.Machine
