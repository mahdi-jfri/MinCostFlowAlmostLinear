module

public import MinCostFlow.Scaling.AdjacencyPushProgram
public import MinCostFlow.Scaling.AdjacencyScan
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# One positive-flow adjacency step

The model's adjacency step prepends an edge exactly when its flow is
positive. Its flow comes from a nonnegative integral solver output and is
stored as an unsigned magnitude. This procedure tests that magnitude,
leaves the table unchanged at zero, and otherwise calls the proved push.
It costs at most 160 steps and allocates at most two words.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[tailVertex,edgeIndex,flowMagnitude,heads,heap]`. -/
def adjacencyStepBody (push : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 4))
    (.call 5 push [.reg 0, .reg 1, .reg 3, .reg 4] ;; .ret (.reg 5))

/-- The conditional model step and the proved positive-flow push. -/
def adjacencyStepModule (b : ℕ) : List Stmt :=
  adjacencyStepBody (b+1) :: adjacencyPushModule (b+1)

/-- A valid stored adjacency table and a fitting possible length increment
suffice for both branches. No traversal conclusion is assumed. -/
def adjacencyStepContract (w lo : ℕ) (J : Circulation) (f : Fin J.m → ℤ)
    (out : Fin J.n → List (Fin J.m)) (e : Fin J.m) : Contract where
  pre args mem := ∃ heads heap,
    args = [(J.tail e).val, e.val, (f e).toNat, heads, heap] ∧ 0 ≤ f e ∧
    AdjacencyAt mem heads lo heap out ∧ heads+2*J.n ≤ lo ∧ lo ≤ heap ∧
    0 < heap ∧ (out (J.tail e)).length+1 < 2 ^ w ∧ ZeroFrom mem heap ∧ heap+2 < 2 ^ w
  post args mem ret mem' := heapArg args ≤ ret ∧ ret ≤ heapArg args+2 ∧
    AdjacencyAt mem' (args.getD 3 0) lo ret (J.adjacencyStep f out e) ∧ ZeroFrom mem' ret ∧
    ∀ x < heapArg args, x ≠ args.getD 3 0+2*(J.tail e).val →
      x ≠ args.getD 3 0+2*(J.tail e).val+1 → mem' x = mem x
  cost _ _ := 160

/-- Conditional insertion and all called procedures use no random instructions. -/
theorem adjacencyStepModule_noRand (b : ℕ) : ∀ body ∈ adjacencyStepModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [adjacencyStepBody, Stmt.NoRand, and_self]
  · exact adjacencyPushModule_noRand _ body hb

/-- The machine computes exactly `Circulation.adjacencyStep` on a
nonnegative integer flow, with explicit cost, frame, and allocation bounds. -/
theorem adjacencyStep_meetsContract {w b lo : ℕ} {p : Program}
    (hp : p.HasAt b (adjacencyStepModule b)) (J : Circulation) (f : Fin J.m → ℤ)
    (out : Fin J.n → List (Fin J.m)) (e : Fin J.m) :
    MeetsContract w p b (adjacencyStepContract w lo J f out e) := by
  have hkP := adjacencyPush_meetsContract (w := w) (lo := lo) (hasAt_tail hp) out (J.tail e) e
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨heads, heap, rfl, hf, hat, hheadsEnd, hlo, hpositive, hlength, hzero, hspace⟩ := hpre
  have ht : (J.tail e).val < 2 ^ w := hwords _ (by simp)
  have he : e.val < 2 ^ w := hwords _ (by simp)
  have hflow : (f e).toNat < 2 ^ w := hwords _ (by simp)
  have hheads : heads < 2 ^ w := hwords _ (by simp)
  have hheap : heap < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold adjacencyStepBody
  wram_step
  · have hz : (f e).toNat = 0 := by simpa [startState] using hcond
    have hnotpos : ¬ 0 < f e := by omega
    refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
    · change heap ≤ heap ∧ heap ≤ heap+2 ∧ AdjacencyAt mem heads lo heap (J.adjacencyStep f out e) ∧
        ZeroFrom mem heap ∧ ∀ x < heap, x ≠ heads+2*(J.tail e).val →
          x ≠ heads+2*(J.tail e).val+1 → mem x = mem x
      simp only [Circulation.adjacencyStep, hnotpos, ↓reduceIte]
      exact ⟨le_rfl, by omega, hat, hzero, fun _ _ _ _ => True.intro⟩
    · simp only [adjacencyStepContract, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
  · have hz : (f e).toNat ≠ 0 := by simpa [startState] using hcond
    have hpos : 0 < f e := by omega
    refine runs_seq_call_le hkP (vs := [(J.tail e).val, e.val, heads, heap]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨heads, heap, rfl, hat, hheadsEnd, hlo, hpositive, hlength, hzero, hspace⟩
    · intro next memP posP hpostP
      obtain ⟨hnext, htableP, hzeroP, hframeP⟩ := hpostP
      change next = heap+2 at hnext
      change AdjacencyAt memP heads lo next (Function.update out (J.tail e) (e :: out (J.tail e))) at htableP
      change (∀ x < heap, x ≠ heads+2*(J.tail e).val → x ≠ heads+2*(J.tail e).val+1 → memP x = mem x) at hframeP
      have hnextWord : next < 2 ^ w := by omega
      refine runs_ret_le (v := next) (by eval_expr) ?_ ?_
      · change heap ≤ next ∧ next ≤ heap+2 ∧ AdjacencyAt memP heads lo next (J.adjacencyStep f out e) ∧
          ZeroFrom memP next ∧ ∀ x < heap, x ≠ heads+2*(J.tail e).val →
            x ≠ heads+2*(J.tail e).val+1 → memP x = mem x
        simp only [Circulation.adjacencyStep, hpos, ↓reduceIte]
        exact ⟨by omega, by omega, htableP, hzeroP, hframeP⟩
      · simp only [adjacencyStepContract, adjacencyPushContract, argsSize_cons,
          argsSize_nil, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega

/-- Empty adjacency initialization gives simultaneous premises for every
edge and nonnegative flow magnitude at a sufficiently large width. -/
theorem exists_adjacencyStep_pre (J : Circulation) (f : Fin J.m → ℤ)
    (e : Fin J.m) (hf : 0 ≤ f e) :
    ∃ w lo, (∀ x ∈ [(J.tail e).val, e.val, (f e).toNat, 0, lo], x < 2 ^ w) ∧
      (adjacencyStepContract w lo J f (fun _ => []) e).pre
        [(J.tail e).val, e.val, (f e).toNat, 0, lo] (fun _ => 0) := by
  let lo := 2*J.n+1
  let w := J.m+2*J.n+(f e).toNat+10
  have hw : J.m+2*J.n+(f e).toNat+10 < 2 ^ w := Nat.lt_two_pow_self
  have ht := (J.tail e).isLt
  have he := e.isLt
  refine ⟨w, lo, ?_, 0, lo, rfl, hf, adjacencyAt_empty (fun _ _ => rfl),
    by dsimp [lo]; omega, le_rfl, by dsimp [lo]; omega,
    by change 0+1 < 2 ^ w; omega, (fun _ _ => rfl), ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> (try dsimp [lo]) <;> omega
  · dsimp [lo]
    omega

end MinCostFlow.Scaling.Machine
