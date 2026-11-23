module

public import MinCostFlow.Num.AddCarry
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Adding two signed limb blocks

The public entry supplies zero as the incoming carry of the limb-adder. The adder's
output is the wrapped signed sum. The two bodies form one module, so callers need
only place `addModule b h` at `b`. The cost is at most `38 * L + 15`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Insert the initial carry into arguments `[a, d, L, heap]`. -/
def addArgs (args : List ℕ) : List ℕ :=
  [args.getD 0 0, args.getD 1 0, args.getD 2 0, 0, args.getD 3 0]

/-- The public addition entry calls its limb-adder with zero carry. -/
def addBody (kernel : ℕ) : Stmt :=
  .call 4 kernel [.reg 0, .reg 1, .reg 2, .const 0, .reg 3] ;; .ret (.reg 4)

/-- Addition and its recursive helper, at consecutive procedure indices. -/
def addModule (b h : ℕ) : List Stmt := [addBody (b + 1), addCarryBody (b + 1) h]

/-- Addition inherits the limb-adder's heap discipline and wrap semantics. -/
def addContract (w h : ℕ) : Contract where
  pre args mem := ∃ a d L heap, args = [a, d, L, heap] ∧
    (addCarryContract w h).pre [a, d, L, 0, heap] mem
  post args mem v mem' := (addCarryContract w h).post (addArgs args) mem v mem'
  cost args _ := 38 * args.getD 2 0 + 15

/-- Neither entry in the addition module uses random bits. -/
theorem addModule_noRand (b h : ℕ) : ∀ s ∈ addModule b h, s.NoRand := by
  simp only [addModule, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨by simp [addBody, Stmt.NoRand], addCarryBody_noRand _ _⟩

/-- The addition module computes a wrapped signed sum within linear time. -/
theorem add_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2 * h + 2 ≤ w) (hp : p.HasAt b (addModule b h)) :
    MeetsContract w p b (addContract w h) := by
  have hkernel : p.HasAt (b + 1) (addCarryModule (b + 1) h) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [addCarryModule, addModule] using hp 1 (by simp [addModule])
  have hk := addCarry_meetsContract hh hw hkernel
  have hentry : p.procs[b]? = some (addBody (b + 1)) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨a, d, L, heap, rfl, hpre⟩
  have hw1 : 0 < 2 ^ w := pow_pos (by decide) w
  apply runs_start_le
  unfold addBody
  refine runs_seq_call_le hk (by eval_expr) ?_ hpre ?_
  · simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] using (show a < 2 ^ w ∧ d < 2 ^ w ∧ L < 2 ^ w ∧
        0 < 2 ^ w ∧ heap < 2 ^ w from
      ⟨hwords a (by simp), hwords d (by simp), hwords L (by simp), hw1,
        hwords heap (by simp)⟩)
  · intro v mem' pos' hpost
    have hv : v = heap + L := hpost.1
    have hb : heap + L < 2 ^ w := hpre.2.2
    have hvword : v < 2 ^ w := by omega
    refine runs_ret_le (v := v) (by eval_expr) hpost ?_
    simp only [addContract, addCarryContract, heapContract, List.getD_cons_zero,
      List.getD_cons_succ, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
    omega

end MinCostFlow.Num
