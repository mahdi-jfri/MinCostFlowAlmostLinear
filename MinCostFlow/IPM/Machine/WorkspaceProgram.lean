module

public import MinCostFlow.IPM.Machine.CoefficientWorkspace
public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic.Linarith

/-!
# Computing coefficient-refresh workspace sizes

The target-test driver reserves whole numerical workspaces. This word
program computes their two sizes from the dimensions and precision,
writes them into a two-word record, and charges each arithmetic step.
All intermediate expressions fit whenever the reserved workspaces fit.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[m,L,P,E,heap]`; output length and gradient array sizes. -/
def workspaceBody : Stmt :=
  .assign 5 (.bin .mul (.reg 1) (.reg 1)) ;;
  .assign 6 (.bin .add (.bin .add (.bin .mul (.const 5) (.reg 5))
    (.bin .mul (.const 24) (.reg 1))) (.const 3)) ;;
  .assign 7 (.bin .add (.bin .mul (.const 11) (.reg 1)) (.const 1)) ;;
  .assign 8 (.bin .add (.bin .mul (.const 3) (.reg 1)) (.const 1)) ;;
  .assign 9 (.bin .add (.bin .add (.bin .add (.bin .add
    (.bin .mul (.const 270) (.reg 5)) (.bin .mul (.const 409) (.reg 1))) (.const 24))
    (.bin .mul (.bin .mul (.const 6) (.bin .add (.reg 2) (.const 4))) (.reg 6)))
    (.bin .add (.bin .mul (.bin .mul (.const 2) (.reg 3)) (.reg 8))
      (.bin .mul (.bin .add (.bin .mul (.const 4) (.reg 3)) (.const 12)) (.reg 7)))) ;;
  .assign 10 (.bin .add (.bin .add (.bin .add (.reg 9)
    (.bin .mul (.const 45) (.reg 5))) (.bin .mul (.const 65) (.reg 1))) (.const 3)) ;;
  .assign 11 (.bin .add (.bin .mul (.bin .add (.reg 0) (.const 1)) (.reg 1))
    (.bin .mul (.reg 0) (.reg 9))) ;;
  .assign 12 (.bin .add (.bin .mul (.bin .add (.reg 0) (.const 1)) (.reg 1))
    (.bin .mul (.reg 0) (.reg 10))) ;;
  .store (.reg 4) (.reg 11) ;;
  .store (.bin .add (.reg 4) (.const 1)) (.reg 12) ;;
  .ret (.bin .add (.reg 4) (.const 2))

/-- A single entry computing the two numerical allocation bounds. -/
def workspaceModule : List Stmt := [workspaceBody]

/-- The workspace record uses two words; the caller also has enough
address space for the numerical workspaces it records. -/
def workspaceContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ m L P E heap,args=[m,L,P,E,heap] ∧ 0 < m ∧ 0 < L ∧
      heap+2+Num.IPM.lengthArraySpace m L P E+Num.IPM.gradientArraySpace m L P E < 2^w)
    (fun args _ mem' => ListAt mem' (heapArg args)
      [Num.IPM.lengthArraySpace (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 3 0),
       Num.IPM.gradientArraySpace (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 3 0)])
    (fun _ _ => 500) (fun _ _ => 2)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+2}

/-- Workspace arithmetic contains no random instruction. -/
theorem workspace_noRand : workspaceBody.NoRand := by
  simp [workspaceBody,Stmt.NoRand]

/-- Both array allocations are computed by word arithmetic without
truncation, with two-word output and full heap framing. -/
theorem workspace_meetsContract {w b : ℕ} {p : Program}
    (hw : 409 < 2^w) (hp : p.HasAt b workspaceModule) :
    MeetsContract w p b (workspaceContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,L,P,E,heap,rfl,hm,hL,hall⟩,hz,hspace⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+2 < 2^w at hspace
  rw [← lengthArrayWorkspace_eq,← gradientArrayWorkspace_eq] at hall
  have hdle := Nat.le_mul_of_pos_left (lengthWorkspace L P E) hm
  have hgle := Nat.le_mul_of_pos_left (gradientWorkspace L P E) hm
  have hd : lengthWorkspace L P E < 2^w := by omega
  have hg : gradientWorkspace L P E < 2^w := by omega
  have hdc : 270*(L*L)+409*L+24+6*(P+4)*(5*(L*L)+24*L+3)+
      2*E*(3*L+1)+(4*E+12)*(11*L+1) < 2^w := by
    simpa only [lengthWorkspace,Nat.mul_assoc] using hd
  have hgc : lengthWorkspace L P E+45*(L*L)+65*L+3 < 2^w := by
    simpa only [gradientWorkspace,Nat.mul_assoc] using hg
  have hA := Nat.le_mul_of_pos_left (5*(L*L)+24*L+3)
    (show 0 < 6*(P+4) by omega)
  have hP4 := Nat.le_mul_of_pos_right (6*(P+4))
    (show 0 < 5*(L*L)+24*L+3 by omega)
  have hE2 := Nat.le_mul_of_pos_right (2*E) (show 0 < 3*L+1 by omega)
  have hE4 := Nat.le_mul_of_pos_right (4*E+12) (show 0 < 11*L+1 by omega)
  have hB := Nat.le_mul_of_pos_left (11*L+1) (show 0 < 4*E+12 by omega)
  have hC := Nat.le_mul_of_pos_left (3*L+1) (show 0 < 409 by decide)
  have hbase : (m+1)*L < 2^w := by omega
  have hm1 := Nat.le_mul_of_pos_right (m+1) hL
  have hlen : (m+1)*L+m*lengthWorkspace L P E < 2^w := by omega
  have hgrad : (m+1)*L+m*gradientWorkspace L P E < 2^w := by omega
  have hform : 270*(L*L)+409*L+24+6*(P+4)*(5*(L*L)+24*L+3)+
      (2*E*(3*L+1)+(4*E+12)*(11*L+1))=lengthWorkspace L P E := by
    unfold lengthWorkspace
    ring
  have hgform : lengthWorkspace L P E+45*(L*L)+65*L+3=gradientWorkspace L P E := by
    unfold gradientWorkspace
    ring
  apply runs_start_le
  unfold workspaceBody
  wram_step
  wram_step
  wram_step
  wram_step
  wram_step
  simp only [hform]
  wram_step
  simp only [hgform]
  wram_step
  wram_step
  wram_step
  wram_step
  refine runs_ret_le (v:=heap+2) (by eval_expr) ?_ ?_
  · change (heap ≤ heap+2 ∧ heap+2 ≤ heap+2 ∧
      (∀ x < heap,_) ∧ ZeroFrom _ (heap+2) ∧ ListAt _ heap
      [Num.IPM.lengthArraySpace m L P E,Num.IPM.gradientArraySpace m L P E]) ∧ _
    refine ⟨⟨by omega,le_rfl,?_,?_,?_⟩,rfl⟩
    · intro x hx
      simp [startState,Function.update_of_ne (by omega : x ≠ heap),
        Function.update_of_ne (by omega : x ≠ heap+1)]
    · intro x hx
      simp only [Function.update_of_ne (by omega : x ≠ heap+1),
        Function.update_of_ne (by omega : x ≠ heap)]
      exact hz x (by omega)
    · intro i hi
      have hii : i < 2 := by simpa using hi
      interval_cases i <;> simp [← lengthArrayWorkspace_eq,← gradientArrayWorkspace_eq]
  · simp only [workspaceContract,heapContract,Expr.size_reg,Expr.size_const,
      Expr.size_bin]
    omega

end MinCostFlow.IPM.Machine
