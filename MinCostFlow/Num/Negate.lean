module

public import MinCostFlow.Num.NegateCarry
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Signed negation

The public entry supplies one as the incoming carry of the complement routine. The
result is the wrapped signed negative of the source value. The most negative input
wraps to itself. All other negations are exact when their signed result fits.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Insert the initial carry into arguments `[a, L, heap]`. -/
def negateArgs (args : List ℕ) : List ℕ :=
  [args.getD 0 0, args.getD 1 0, 1, args.getD 2 0]

/-- Negation calls its complement helper with carry one. -/
def negateBody (kernel : ℕ) : Stmt :=
  .call 3 kernel [.reg 0, .reg 1, .const 1, .reg 2] ;; .ret (.reg 3)

/-- The public negation entry and its recursive helper. -/
def negateModule (b h : ℕ) : List Stmt := [negateBody (b + 1), negateCarryBody (b + 1) h]

/-- Negation inherits the helper's exact heap pointer and stored digit list. -/
def negateContract (w h : ℕ) : Contract where
  pre args mem := ∃ a L heap, args = [a, L, heap] ∧
    (negateCarryContract w h).pre [a, L, 1, heap] mem
  post args mem v mem' := (negateCarryContract w h).post (negateArgs args) mem v mem'
  cost args _ := 36 * args.getD 1 0 + 14

/-- The complete negation module uses no random bits. -/
theorem negateModule_noRand (b h : ℕ) : ∀ s ∈ negateModule b h, s.NoRand := by
  simp only [negateModule, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  exact ⟨by simp [negateBody, Stmt.NoRand], negateCarryBody_noRand _ _⟩

/-- Negation meets its contract at cost at most `36 * L + 14`. -/
theorem negate_meetsContract {w h b : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w) (hp : p.HasAt b (negateModule b h)) :
    MeetsContract w p b (negateContract w h) := by
  have hkernel : p.HasAt (b + 1) (negateCarryModule (b + 1) h) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [negateCarryModule, negateModule] using hp 1 (by simp [negateModule])
  have hk := negateCarry_meetsContract hw hb hkernel
  have hentry : p.procs[b]? = some (negateBody (b + 1)) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨a, L, heap, rfl, hpre⟩
  apply runs_start_le
  unfold negateBody
  refine runs_seq_call_le hk (by eval_expr) ?_ hpre ?_
  · simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] using (show a < 2 ^ w ∧ L < 2 ^ w ∧ 1 < 2 ^ w ∧ heap < 2 ^ w from
      ⟨hwords a (by simp), hwords L (by simp), hw, hwords heap (by simp)⟩)
  · intro v mem' pos' hpost
    have hv : v = heap + L := hpost.1
    have hbound : heap + L < 2 ^ w := hpre.2.2
    have hvword : v < 2 ^ w := by omega
    refine runs_ret_le (v := v) (by eval_expr) hpost ?_
    simp only [negateContract, negateCarryContract, heapContract, List.getD_cons_zero,
      List.getD_cons_succ, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
    omega

end MinCostFlow.Num
