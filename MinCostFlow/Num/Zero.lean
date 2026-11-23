module

public import MinCostFlow.Num.Representation
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Allocating a zero fixed-point number

The shared heap convention guarantees zero memory at the heap pointer. Zero allocation
therefore only advances that pointer. It needs no limb stores, costs four steps, and
works for every block length, including zero. The returned pointer marks the end of the
new block. This implements zero for the fixed-point model on page 7.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments are `[L, heap]`. The new zero block starts at `heap`. -/
def zeroBody : Stmt := .ret (.bin .add (.reg 0) (.reg 1))

/-- A zero-allocation module, placed at procedure index `b`. -/
def zeroModule (_b : ℕ) : List Stmt := [zeroBody]

/-- Allocates `L` zero limbs at the old heap pointer, returning the new pointer.
The body cost is four, hence also at most `4 * (L + 1)`. -/
def zeroContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ L heap, args = [L, heap])
    (fun args _ mem' =>
      Valid mem' (heapArg args) h (args.getD 0 0) ∧
      intVal mem' (heapArg args) h (args.getD 0 0) = 0)
    (fun _ _ => 4) (fun args _ => args.getD 0 0)
  { C with post := fun args mem v mem' =>
      v = heapArg args + args.getD 0 0 ∧ C.post args mem v mem' }

/-- Zero allocation is deterministic. -/
theorem zeroBody_noRand : zeroBody.NoRand := by trivial

/-- The zero module meets the common heap contract, for every random tape. -/
theorem zero_meetsContract {w h b : ℕ} {p : Program}
    (hp : p.HasAt b (zeroModule b)) : MeetsContract w p b (zeroContract w h) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω _ hpre
  rcases hpre with ⟨⟨L, heap, rfl⟩, hz, hb⟩
  simp only [heapArg, List.getLastD_cons, List.getLastD_nil, List.getD_cons_zero] at hz hb
  refine runs_start_le ?_
  unfold zeroBody
  refine runs_ret_le (by eval_expr) ?_ (by simp [zeroContract, heapContract])
  refine ⟨by change L + heap = heap + L; omega, ?_⟩
  change heap ≤ L + heap ∧ L + heap ≤ heap + L ∧
    (∀ x < heap, mem x = mem x) ∧ ZeroFrom mem (L + heap) ∧
    Valid mem heap h L ∧ intVal mem heap h L = 0
  exact ⟨by omega, by omega, fun _ _ => rfl, hz.mono (by omega),
    zeroFrom_valid hz le_rfl, intVal_zeroFrom hz le_rfl⟩

end MinCostFlow.Num
