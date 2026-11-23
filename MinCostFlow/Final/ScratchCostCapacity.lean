module

public import MinCostFlow.Final.ScratchCostScaling
public import MinCostFlow.Scaling.CostCapacityContract
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.CostScalingProgram
import MinCostFlow.Scaling.CostScalingSpace
import MinCostFlow.Scaling.CostScalingWorkLower
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Selecting the capacity budget with polynomial scratch

The wrapper computes the augmented capacity bound and calls the widened
cost-scaling module.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Budget augmentation followed by the complete cost-scaling module. -/
def scratchCostCapacityModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  costCapacityBody (b+1) :: scratchCostScalingModule solver entry (b+1) c d

/-- Exact complete cost-capacity model on arbitrary natural capacities
and bounded integer costs, with its actual primitive-call and work budget. -/
noncomputable def scratchCostCapacityContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C U : ℕ) : Contract :=
  let V := max U (2*J.m+1)
  let r := costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J C U
  { pre := fun args mem => ∃ a heap,args=[a,C,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
      ZeroFrom mem heap ∧ heap+scratchCostScalingSpace c d J C V<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+scratchCostScalingSpace c d J C V ∧
      ListAt mem' (ret-J.m) (List.ofFn (fun e => (r.value e).toNat)) ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => r.calls.length*((solver.regBound+6)*T (J.compress.n+3) (16*J.m+4*J.compress.n))+
      303000*scratchWorkFactor solver c d*r.work }

/-- Budget selection and the full nested scaling program use no random instruction. -/
theorem scratchCostCapacityModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchCostCapacityModule solver entry b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [costCapacityBody,Stmt.NoRand,and_self]
  · exact scratchCostScalingModule_noRand solver entry _ c d hdet body hb

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
theorem scratchCostCapacity_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (scratchCostCapacityModule solver entry b c d)) (J : Circulation) (C U : ℕ) :
    MeetsContract w p b (scratchCostCapacityContract w solver entry T S c d hproc J C U) := by
  let V := max U (2*J.m+1)
  let r := costCapacityModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J C U
  let Q := r.calls.length*((solver.regBound+6)*T (J.compress.n+3) (16*J.m+4*J.compress.n))
  have hk := scratchCostScaling_meetsContract (w := w) hproc hScratch hdet hmono (hasAt_tail hp) J C V
  have hwork : 1≤r.work := costCapacityModel_work_pos ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J C U
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hC,hu,hz,hs⟩ := hpre
  have huV : ∀ e,J.capacity e≤V := fun e => (hu e).trans (le_max_left _ _)
  obtain ⟨h8,_,_,_⟩ := scratchCostScaling_words_of_space c d J C V heap hC huV hs
  have hspace := hs
  unfold scratchCostScalingSpace at hspace
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
  have hchildPre : (scratchCostScalingContract w solver entry T S c d hproc J C V).pre [a,C,V,heap] mem :=
    ⟨a,heap,rfl,hgraph,hgraphEnd,hC,huV,le_max_right _ _,hz,hs⟩
  let charge := (scratchCostScalingContract w solver entry T S c d hproc J C V).cost [a,C,V,heap] mem
  have hS : charge=Q+302000*scratchWorkFactor solver c d*r.work := rfl
  have hpad := capacity_entry_padding Q r.work (scratchWorkFactor solver c d - 1) charge hwork
    (by simpa only [scratchWorkFactor_succ] using hS)
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
      · change _≤Q+303000*scratchWorkFactor solver c d*r.work
        apply le_trans (b := 100+charge) ?_ (by simpa only [scratchWorkFactor_succ] using hpad)
        simp only [argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        have hc : (scratchCostScalingContract w solver entry T S c d hproc J C V).cost
            [a,C,V,heap] (startState [a,C,U,heap] mem pos).mem = charge := rfl
        rw [hc]
        omega
  · have hV : V=U := max_eq_left (by omega)
    refine runs_seq_call_le hk (vs := [a,C,V,heap]) ?_ (by wram_words) hchildPre ?_
    · rw [hV]
      exact capacity_entry_old_args (by rfl) (by rfl) (by rfl) (by rfl)
    · intro ret memS posS hpostS
      refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
      · exact hpostS
      · change _≤Q+303000*scratchWorkFactor solver c d*r.work
        apply le_trans (b := 100+charge) ?_ (by simpa only [scratchWorkFactor_succ] using hpad)
        simp only [argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        have hc : (scratchCostScalingContract w solver entry T S c d hproc J C V).cost
            [a,C,V,heap] (startState [a,C,U,heap] mem pos).mem = charge := rfl
        rw [hc]
        omega

end MinCostFlow.Final
