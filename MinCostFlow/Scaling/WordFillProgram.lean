module

public import MinCostFlow.Scaling.SolverContract
import WordRAM.Logic
import WordRAM.Tactic

/-!
# Filling a fresh word array

The shortest-routing initial flow consists of zero words followed by one
words. This procedure writes a constant array into fresh memory, with exact
allocation and a linear cost. It is used to assemble that model vector.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[count,value,heap]`. -/
def wordFillBody (self : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 0) (.const 0)) (.ret (.reg 2))
    (.store (.reg 2) (.reg 1) ;;
     .call 3 self [.bin .sub (.reg 0) (.const 1), .reg 1, .bin .add (.reg 2) (.const 1)] ;;
     .ret (.reg 3))

/-- A single recursive filling procedure. -/
def wordFillModule (b : ℕ) : List Stmt := [wordFillBody b]

/-- Exact allocation and the contiguous constant-array result. -/
def wordFillContract (w count value : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ heap, args = [count, value, heap] ∧ value < 2^w ∧ 1 < 2^w)
    (fun args _ mem' => ListAt mem' (heapArg args) (List.replicate count value))
    (fun _ _ => 40*count+20) (fun _ _ => count)
  { C with post := fun args mem ret mem' => C.post args mem ret mem' ∧ ret = heapArg args+count }

/-- Filling uses no random instruction. -/
theorem wordFillBody_noRand (b : ℕ) : (wordFillBody b).NoRand := by
  simp only [wordFillBody, Stmt.NoRand, and_self]

/-- The filling loop writes exactly the requested constant array. -/
theorem wordFill_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (wordFillModule b)) (count value : ℕ) :
    MeetsContract w p b (wordFillContract w count value) := by
  induction count with
  | zero =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨heap, rfl, _, _⟩, hz, hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+0 < 2^w at hs
    have hh : heap < 2^w := by omega
    apply runs_start_le
    unfold wordFillBody
    wram_step
    · refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · change (heap ≤ heap ∧ heap ≤ heap+0 ∧ (∀ x < heap, mem x = mem x) ∧
          ZeroFrom mem heap ∧ ListAt mem heap []) ∧ heap = heap+0
        exact ⟨⟨le_rfl, by omega, fun _ _ => rfl, hz, listAt_nil _ _⟩, by omega⟩
      · simp only [wordFillContract, heapContract, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
  | succ count ih =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨heap, rfl, hv, hw⟩, hz, hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+(count+1) < 2^w at hs
    have hh : heap < 2^w := by omega
    have hh1 : heap+1 < 2^w := by omega
    have hn := hwords (count+1) (List.mem_cons_self)
    have hn' : count < 2^w := by omega
    let memS := Function.update mem heap value
    have hzeroS : ZeroFrom memS (heap+1) := by
      intro x hx
      dsimp only [memS]
      rw [Function.update_of_ne (by omega : x ≠ heap)]
      exact hz x (by omega)
    apply runs_start_le
    unfold wordFillBody
    wram_step
    wram_step
    refine runs_seq_call_le ih (vs := [count, value, heap+1]) ?_ ?_ ?_ ?_
    · conv_rhs => rw [← Nat.add_sub_cancel count 1]
      eval_expr
    · wram_words
    · exact ⟨⟨heap+1, rfl, hv, hw⟩, hzeroS, by change heap+1+count < 2^w; omega⟩
    · intro ret memR posR hpost
      obtain ⟨⟨_, _, hframe, hzR, hat⟩, hret⟩ := hpost
      change ret = heap+1+count at hret
      change (∀ x < heap+1, memR x = memS x) at hframe
      change ZeroFrom memR ret at hzR
      change ListAt memR (heap+1) (List.replicate count value) at hat
      have hr : ret < 2^w := by omega
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · change (heap ≤ ret ∧ ret ≤ heap+(count+1) ∧ (∀ x < heap, memR x = mem x) ∧
          ZeroFrom memR ret ∧ ListAt memR heap (List.replicate (count+1) value)) ∧
          ret = heap+(count+1)
        refine ⟨⟨by omega, by omega, ?_, hzR, ?_⟩, by omega⟩
        · intro x hx
          rw [hframe x (by omega)]
          exact Function.update_of_ne (by omega : x ≠ heap) _ _
        · rw [List.replicate_succ]
          apply listAt_cons.mpr
          exact ⟨(hframe heap (by omega)).trans (Function.update_self _ _ _), hat⟩
      · simp only [wordFillContract, heapContract, argsSize_cons, argsSize_nil,
          Expr.size_bin, Expr.size_reg, Expr.size_const]; omega

/-- Every count and value have simultaneous argument and fresh-space bounds. -/
theorem exists_wordFill_pre (count value : ℕ) :
    ∃ w args mem, (∀ x ∈ args, x < 2^w) ∧ (wordFillContract w count value).pre args mem := by
  let w := count+value+3
  have hw : count+value+3 < 2^w := Nat.lt_two_pow_self
  refine ⟨w, [count,value,0], (fun _ => 0), ?_, ⟨0, rfl, by omega, by omega⟩,
    (fun _ _ => rfl), ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · change 0+count < 2^w
    omega

end MinCostFlow.Scaling.Machine
