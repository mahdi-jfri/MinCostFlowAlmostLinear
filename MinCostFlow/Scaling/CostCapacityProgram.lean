module

public import MinCostFlow.Scaling.CostCapacityContract
import MinCostFlow.Scaling.CostScalingProgram
import MinCostFlow.Scaling.CostScalingSpace
import MinCostFlow.Scaling.CostScalingWorkLower
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Executing the exact cost-capacity model

Compute the model's capacity budget by comparing `U` with `2*m+1`.
Both branches call the same complete measured cost-scaling procedure
with that exact maximum. Its returned flow and memory frames are retained.
The model's positive work pays for the constant augmentation overhead.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem capacity_entry_padding (Q W reg S : ℕ) (hW : 1≤W)
    (hS : S=Q+302000*(reg+1)*W) : 100+S≤Q+303000*(reg+1)*W := by
  rw [hS]
  have hRW : 1≤(reg+1)*W := Nat.mul_pos (by omega) hW
  simp only [Nat.mul_assoc]
  omega

private theorem capacity_entry_m_eval {w a m : ℕ} {st : State} (h0 : st.regs 0=a)
    (ha : a+1<2^w) (hm : st.mem (a+1)=m) :
    Expr.eval w st (.load (.bin .add (.reg 0) (.const 1)))=some m := by eval_expr

private theorem capacity_entry_budget_eval {w m : ℕ} {st : State} (h4 : st.regs 4=m)
    (h2 : 2<2^w) (hprod : 2*m<2^w) (hbound : 2*m+1<2^w) :
    Expr.eval w st (.bin .add (.bin .mul (.const 2) (.reg 4)) (.const 1))=some (2*m+1) := by eval_expr

private theorem capacity_entry_new_args {w a C V heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h1 : st.regs 1=C) (h5 : st.regs 5=V) (h3 : st.regs 3=heap) :
    evalArgs w st [.reg 0,.reg 1,.reg 5,.reg 3]=some [a,C,V,heap] := by eval_expr

private theorem capacity_entry_old_args {w a C U heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h1 : st.regs 1=C) (h2 : st.regs 2=U) (h3 : st.regs 3=heap) :
    evalArgs w st [.reg 0,.reg 1,.reg 2,.reg 3]=some [a,C,U,heap] := by eval_expr

/-- Capacity-budget augmentation and complete measured cost scaling return
exactly `costCapacityModel`, with its actual primitive-call term and
`303000*(regBound+1)*work` bound on all machine instructions. -/
theorem costCapacity_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (costCapacityModule solver entry b)) (J : Circulation) (C U : ℕ) :
    MeetsContract w p b (costCapacityContract w solver entry T hproc J C U) := by
  let V := max U (2*J.m+1)
  let r := costCapacityModel (canonicalSolver solver entry T hproc) J C U
  let Q := r.calls.length*((solver.regBound+6)*T (J.compress.n+3) (16*J.m+4*J.compress.n))
  have hk := costScaling_meetsContract (w := w) hproc hdet hmono (hasAt_tail hp) J C V
  have hwork : 1≤r.work := costCapacityModel_work_pos (canonicalSolver solver entry T hproc) J C U
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hC,hu,hz,hs⟩ := hpre
  have huV : ∀ e,J.capacity e≤V := fun e => (hu e).trans (le_max_left _ _)
  obtain ⟨h8,_,_,_⟩ := costScaling_words_of_space J C V heap hC huV hs
  have hspace := hs
  unfold costScalingSpace at hspace
  rw [J.solverWords_length] at hspace
  have hbound : 2*J.m+1<2^w := by omega
  have hprod : 2*J.m<2^w := by omega
  have hCword : C<2^w := hwords C (by simp)
  have hUword : U<2^w := hwords U (by simp)
  have hh : heap<2^w := by omega
  have haWord : a<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hmWord : J.m<2^w := by omega
  have hVword : V<2^w := max_lt hUword hbound
  have hM := (solver_header_at J hgraph).2
  have hchildPre : (costScalingContract w solver entry T hproc J C V).pre [a,C,V,heap] mem :=
    ⟨a,heap,rfl,hgraph,hgraphEnd,hC,huV,le_max_right _ _,hz,hs⟩
  let S := (costScalingContract w solver entry T hproc J C V).cost [a,C,V,heap] mem
  have hS : S=Q+302000*(solver.regBound+1)*r.work := rfl
  have hpad := capacity_entry_padding Q r.work solver.regBound S hwork hS
  apply runs_start_le
  unfold costCapacityBody
  refine runs_seq_assign_le (v := J.m) (capacity_entry_m_eval (by rfl) ha1 hM) ?_
  refine runs_seq_assign_le (v := 2*J.m+1) (capacity_entry_budget_eval (by rfl) (by omega) hprod hbound) ?_
  wram_step
  · have hV : V=2*J.m+1 := max_eq_right (by omega)
    refine runs_seq_call_le hk (vs := [a,C,V,heap]) ?_ (by wram_words) hchildPre ?_
    · rw [hV]
      exact capacity_entry_new_args (by rfl) (by rfl) (by rfl) (by rfl)
    · intro ret memS posS hpostS
      refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
      · exact hpostS
      · change _≤Q+303000*(solver.regBound+1)*r.work
        apply le_trans (b := 100+S) ?_ hpad
        simp only [argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        have hc : (costScalingContract w solver entry T hproc J C V).cost
            [a,C,V,heap] (startState [a,C,U,heap] mem pos).mem = S := rfl
        rw [hc]
        omega
  · have hV : V=U := max_eq_left (by omega)
    refine runs_seq_call_le hk (vs := [a,C,V,heap]) ?_ (by wram_words) hchildPre ?_
    · rw [hV]
      exact capacity_entry_old_args (by rfl) (by rfl) (by rfl) (by rfl)
    · intro ret memS posS hpostS
      refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
      · exact hpostS
      · change _≤Q+303000*(solver.regBound+1)*r.work
        apply le_trans (b := 100+S) ?_ hpad
        simp only [argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        have hc : (costScalingContract w solver entry T hproc J C V).cost
            [a,C,V,heap] (startState [a,C,U,heap] mem pos).mem = S := rfl
        rw [hc]
        omega

end MinCostFlow.Scaling.Machine
