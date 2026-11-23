module

public import MinCostFlow.Num.Representation
public import WordRAM.Logic
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Copying a limb block

A forward loop copies `L` limbs from an existing block to fresh heap memory. The source
ends at or below the heap pointer. The loop preserves memory below the heap, copies the
prefix already visited, and keeps the remaining heap zero. The contract gives both limb
agreement and equality of decoded signed values. The cost is at most `17 * L + 12`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[src, L, heap]`. Register 3 is the loop index. -/
def copyBody : Stmt :=
  forRange 3 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 2) (.reg 3))
      (.load (.bin .add (.reg 0) (.reg 3)))) ;;
  .ret (.bin .add (.reg 2) (.reg 1))

/-- The copy procedure at index `b`. -/
def copyModule (_b : ℕ) : List Stmt := [copyBody]

/-- Copy a valid source block below the heap into `L` newly allocated cells. -/
def copyContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ src L heap, args = [src, L, heap] ∧
      src + L ≤ heap ∧ Valid mem src h L)
    (fun args mem mem' =>
      (∀ i < args.getD 1 0, mem' (heapArg args + i) = mem (args.getD 0 0 + i)) ∧
      Valid mem' (heapArg args) h (args.getD 1 0) ∧
      intVal mem' (heapArg args) h (args.getD 1 0) =
        intVal mem (args.getD 0 0) h (args.getD 1 0))
    (fun args _ => 17 * args.getD 1 0 + 12) (fun args _ => args.getD 1 0)
  { C with post := fun args mem v mem' =>
      v = heapArg args + args.getD 1 0 ∧ C.post args mem v mem' }

/-- The copy loop contains no random statement. -/
theorem copyBody_noRand : copyBody.NoRand := by
  simp [copyBody, forRange, forUp, Stmt.NoRand]

private theorem copyLoop {w src L heap : ℕ} (p : Program) (mem : ℕ → ℕ) (pos : ℕ)
    (hw : 1 < 2 ^ w) (hb : heap + L < 2 ^ w) (hs : src + L ≤ heap)
    (hz : ZeroFrom mem heap) :
    Triple w p (fun st => st = startState [src, L, heap] mem pos)
      (forRange 3 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 2) (.reg 3))
          (.load (.bin .add (.reg 0) (.reg 3)))))
      (normalPost fun st => st.regs 1 = L ∧ st.regs 2 = heap ∧
        (∀ i < L, st.mem (heap + i) = mem (src + i)) ∧
        (∀ x < heap, st.mem x = mem x) ∧ ZeroFrom st.mem (heap + L))
      (fun _ => 17 * L + 7) := by
  have hl := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 2) (.reg 3))
      (.load (.bin .add (.reg 0) (.reg 3))))
    (P := fun st => st = startState [src, L, heap] mem pos)
    (Inv := fun i st => st.regs 0 = src ∧ st.regs 1 = L ∧ st.regs 2 = heap ∧
      st.regs 3 = i ∧ (∀ j < i, st.mem (heap + j) = mem (src + j)) ∧
      (∀ x < heap, st.mem x = mem x) ∧ ZeroFrom st.mem (heap + i))
    8 0 L (Nat.zero_le L) hw (fun _ => by omega)
    (fun st hst => by
      subst st
      refine ⟨by eval_expr, ?_⟩
      simpa [startState] using hz)
    (fun _ _ _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by
      have h1 := hi.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω hst
      rcases hst with ⟨h0, h1, h2, h3, hcopy, hframe, hzero⟩
      have hread : st.mem (src + i) = mem (src + i) := hframe _ (by omega)
      apply runs_start_le
      refine runs_store_le (by eval_expr) (by eval_expr) ?_ ?_
      · change (_ ∧ _) ∧ _
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h3⟩
        · simpa using h0
        · simpa using h1
        · simpa using h2
        · simp
        · intro j hj
          dsimp only
          by_cases he : j = i
          · subst j
            simp [hread]
          · rw [Function.update_of_ne (by omega)]
            exact hcopy j (by omega)
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hframe x hx
        · simpa [Nat.add_assoc] using hzero.update_head (st.mem (src + i))
      · wram_cost)
  refine hl.conseq (fun _ he => he) ?_ ?_
  · intro o st ho
    cases o with
    | returned v => exact False.elim ho
    | normal => exact ⟨ho.2.1, ho.2.2.1, ho.2.2.2.2⟩
  · intro _ _
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]
    omega

/-- The copy module preserves the source, allocates its copy, and costs at most
`17 * L + 12` machine steps for every random tape. -/
theorem copy_meetsContract {w h b : ℕ} {p : Program} (hw : 1 < 2 ^ w)
    (hp : p.HasAt b (copyModule b)) : MeetsContract w p b (copyContract w h) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω _ hpre
  rcases hpre with ⟨⟨src, L, heap, rfl, hs, hv⟩, hz, hb⟩
  change ZeroFrom mem heap at hz
  change heap + L < 2 ^ w at hb
  apply runs_start_le
  unfold copyBody
  refine runs_seq_triple_le (copyLoop p mem pos hw hb hs hz) rfl ?_
  intro st ⟨h1, h2, hc, hf, hz'⟩
  refine runs_ret_le (by eval_expr) ?_ ?_
  · refine ⟨rfl, ?_⟩
    change heap ≤ heap + L ∧ heap + L ≤ heap + L ∧
      (∀ x < heap, st.mem x = mem x) ∧ ZeroFrom st.mem (heap + L) ∧
      (∀ i < L, st.mem (heap + i) = mem (src + i)) ∧
      Valid st.mem heap h L ∧ intVal st.mem heap h L = intVal mem src h L
    exact ⟨by omega, le_rfl, hf, hz', hc, fun i hi => (hc i hi) ▸ hv i hi,
      intVal_congr hc⟩
  · simp only [copyContract, heapContract, List.getD_cons_succ, List.getD_cons_zero,
      Expr.size_bin, Expr.size_reg]
    omega

end MinCostFlow.Num
