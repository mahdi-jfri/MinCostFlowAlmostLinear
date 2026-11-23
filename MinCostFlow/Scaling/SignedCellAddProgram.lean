module

public import MinCostFlow.Scaling.SignedAddProgram
import WordRAM.Tactic
import WordRAM.Memory
import WordRAM.Entry

/-!
# Adding a contribution to a stored signed demand

The lower-capacity reduction updates two demand entries for each edge.
This helper reads one stored canonical signed integer, adds the supplied
signed contribution with the proved addition procedure, and copies the
result back to the same two cells. Two fresh scratch words are allocated.
Every other cell below the old heap is preserved, and the cost is at most 180.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[cell,contributionSign,contributionMagnitude,heap]`. -/
def signedCellAddBody (add : ℕ) : Stmt :=
  .call 4 add [.load (.reg 0), .load (.bin .add (.reg 0) (.const 1)),
    .reg 1, .reg 2, .reg 3] ;;
  .store (.reg 0) (.load (.reg 3)) ;;
  .store (.bin .add (.reg 0) (.const 1)) (.load (.bin .add (.reg 3) (.const 1))) ;;
  .ret (.reg 4)

/-- In-place demand addition and the existing allocating addition module. -/
def signedCellAddModule (b : ℕ) : List Stmt :=
  signedCellAddBody (b + 1) :: signedAddModule (b + 1)

/-- Only the chosen signed cell and two fresh scratch words may change. -/
def signedCellAddContract (w : ℕ) (x y : ℤ) : Contract where
  pre args mem := ∃ cell heap, args = [cell, if y < 0 then 1 else 0, y.natAbs, heap] ∧
    ListAt mem cell (encodeInt x) ∧ cell + 2 ≤ heap ∧
    x.natAbs + y.natAbs < 2 ^ w ∧ ZeroFrom mem heap ∧ heap + 2 < 2 ^ w
  post args mem out mem' := out = heapArg args + 2 ∧
    ListAt mem' (args.getD 0 0) (encodeInt (x + y)) ∧ ZeroFrom mem' out ∧
    ∀ a < heapArg args, a ≠ args.getD 0 0 → a ≠ args.getD 0 0 + 1 → mem' a = mem a
  cost _ _ := 180

/-- Stored demand addition and all helper procedures have no random instructions. -/
theorem signedCellAddModule_noRand (b : ℕ) :
    ∀ body ∈ signedCellAddModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [signedCellAddBody, Stmt.NoRand, and_self]
  · exact signedAddModule_noRand _ body hb

/-- The demand-cell helper computes exact canonical addition, preserves all
other old cells, and uses two fresh scratch words in at most 180 steps. -/
theorem signedCellAdd_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (signedCellAddModule b)) (x y : ℤ) :
    MeetsContract w p b (signedCellAddContract w x y) := by
  have hadd : p.HasAt (b + 1) (signedAddModule (b + 1)) := by
    intro i hi
    have h := hp (i + 1) (by simp only [signedCellAddModule, List.length_cons]; omega)
    have hi' : b + (i + 1) = (b + 1) + i := by omega
    rw [hi'] at h
    simpa only [signedCellAddModule, List.getElem_cons_succ] using h
  have hk := signedAdd_meetsContract (w := w) hadd x y
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨cell, heap, rfl, hcell, hbefore, hsum, hzero, hspace⟩ := hpre
  have hxs : mem cell = if x < 0 then 1 else 0 := by
    simpa only [encodeInt, List.getElem_cons_zero, Nat.add_zero] using hcell 0 (by change 0 < 2; decide)
  have hxm : mem (cell + 1) = x.natAbs := by
    simpa only [encodeInt, List.getElem_cons_succ, List.getElem_cons_zero] using hcell 1 (by change 1 < 2; decide)
  have hc : cell < 2 ^ w := by omega
  have hc1 : cell + 1 < 2 ^ w := by omega
  have hh : heap < 2 ^ w := by omega
  have hh1 : heap + 1 < 2 ^ w := by omega
  have hx : x.natAbs < 2 ^ w := by omega
  have hy : y.natAbs < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hsx : (if x < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  have hsy : (if y < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
  apply runs_start_le
  unfold signedCellAddBody
  refine runs_seq_call_le hk
    (vs := [if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs, heap])
    (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨heap, rfl, hsum⟩, hzero, hspace⟩
  · intro out memA posA hpost
    obtain ⟨⟨_, _, hframe, hzeroA, hresult⟩, hout⟩ := hpost
    change out = heap + 2 at hout
    change ZeroFrom memA out at hzeroA
    change (∀ a < heap, memA a = mem a) at hframe
    change ListAt memA heap (encodeInt (x + y)) at hresult
    have hsign : memA heap = if x + y < 0 then 1 else 0 := by
      simpa only [encodeInt, List.getElem_cons_zero, Nat.add_zero] using hresult 0 (by change 0 < 2; decide)
    have hmag : memA (heap + 1) = (x + y).natAbs := by
      simpa only [encodeInt, List.getElem_cons_succ, List.getElem_cons_zero] using hresult 1 (by change 1 < 2; decide)
    have hsword : (if x + y < 0 then 1 else 0 : ℕ) < 2 ^ w := by split <;> omega
    have hmword : (x + y).natAbs < 2 ^ w :=
      lt_of_le_of_lt (Int.natAbs_add_le _ _) hsum
    have houtword : out < 2 ^ w := by omega
    refine runs_seq_store_le (by eval_expr) (v := if x + y < 0 then 1 else 0) (by eval_expr) ?_
    have hloadmag : (Function.update memA cell (if x + y < 0 then 1 else 0)) (heap + 1) =
        (x + y).natAbs := by
      rw [Function.update_of_ne (by omega : heap + 1 ≠ cell), hmag]
    refine runs_seq_store_le (by eval_expr) (v := (x + y).natAbs) (by eval_expr) ?_
    refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
    · change out = heap + 2 ∧
        ListAt (Function.update (Function.update memA cell (if x + y < 0 then 1 else 0))
          (cell + 1) (x + y).natAbs) cell (encodeInt (x + y)) ∧
        ZeroFrom (Function.update (Function.update memA cell (if x + y < 0 then 1 else 0))
          (cell + 1) (x + y).natAbs) out ∧
        ∀ a < heap, a ≠ cell → a ≠ cell + 1 →
          Function.update (Function.update memA cell (if x + y < 0 then 1 else 0))
            (cell + 1) (x + y).natAbs a = mem a
      refine ⟨hout, ?_, ?_, ?_⟩
      · intro i hi
        have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
        rcases hi' with rfl | rfl <;>
          simp only [Nat.add_zero, Function.update_self,
            Function.update_of_ne (by omega : cell ≠ cell + 1),
            encodeInt, List.getElem_cons_zero, List.getElem_cons_succ]
      · intro a ha
        rw [Function.update_of_ne (by omega : a ≠ cell + 1),
          Function.update_of_ne (by omega : a ≠ cell)]
        exact hzeroA a ha
      · intro a ha hne hne'
        rw [Function.update_of_ne hne', Function.update_of_ne hne]
        exact hframe a ha
    · simp only [signedCellAddContract, signedAddContract, heapContract,
        argsSize_cons, argsSize_nil, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega

/-- Arbitrary signed inputs satisfy the cell-update premises together on
a concrete two-word table, for a sufficiently large width. -/
theorem exists_signedCellAdd_pre (x y : ℤ) :
    ∃ w, (∀ a ∈ [0, if y < 0 then 1 else 0, y.natAbs, 2], a < 2 ^ w) ∧
      (signedCellAddContract w x y).pre [0, if y < 0 then 1 else 0, y.natAbs, 2]
        (initMem (encodeInt x)) := by
  let w := wordSize 1 [x.natAbs + y.natAbs + 10]
  have hlarge : x.natAbs + y.natAbs + 10 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  refine ⟨w, ?_, 0, 2, rfl, listAt_initMem _, by omega, by omega, ?_, by omega⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · omega
    · split <;> omega
    · omega
    · omega
  · simpa only [encodeInt, List.length_cons, List.length_nil] using zeroFrom_initMem (encodeInt x)

end MinCostFlow.Scaling.Machine
