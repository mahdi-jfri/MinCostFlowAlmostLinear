module

public import MinCostFlow.Scaling.TableBoundProgram
public import MinCostFlow.Scaling.InputLayout
public import MinCostFlow.Scaling.DemandBoundCheck
import WordRAM.Tactic

/-!
# The demand rejection procedure on the statement's input

The general-flow reduction in Appendix C first rejects demands with magnitude
above `m*U`. This procedure reads the two input header words, computes the
first demand magnitude address and the bound, and invokes the strided table
scanner. It implements `demandBoundCheck` on `Instance.encode`, preserves
memory, uses no random instructions, and costs at most `24*n+100`.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Reading the demand magnitude table computes the model's rejection test. -/
theorem tableBoundCheck_demand (I : Instance) (hv : I.IsValid) (U : ℕ)
    (mem : ℕ → ℕ) (a : ℕ) (hat : ListAt mem a I.encode) :
    tableBoundCheck mem (a + 3 + 8 * I.m) 2 I.n (I.m * U) =
      FlowReduction.demandBoundCheck I U := by
  apply Bool.eq_iff_iff.mpr
  rw [tableBoundCheck_iff, FlowReduction.demandBoundCheck_iff]
  have hread (i : ℕ) (hi : i < I.n) :
      mem (a + 3 + 8 * I.m + 2 * i) = (I.d i).natAbs := by
    have hh := demand_magnitude_at I hv mem a hat ⟨i, hi⟩
    have he : a + 3 + 8 * I.m + 2 * i = a + (2 + 8 * I.m + 2 * i + 1) := by omega
    rw [he]
    exact hh
  constructor
  · intro h v
    have hh := h v.val v.isLt
    rw [hread v.val v.isLt] at hh
    exact hh
  · intro h i hi
    rw [hread i hi]
    exact h ⟨i, hi⟩

/-- Arguments `[inputAddress, U]`; the scan procedure is at `scan`. -/
def demandCheckBody (scan : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 4 scan [
    .bin .add (.bin .add (.reg 0) (.const 3)) (.bin .mul (.const 8) (.reg 3)),
    .reg 2, .const 2, .bin .mul (.reg 3) (.reg 1)] ;;
  .ret (.reg 4)

/-- The entry procedure and its shared strided-table helper. -/
def demandCheckModule (b : ℕ) : List Stmt :=
  [demandCheckBody (b + 1), tableBoundBody (b + 1)]

/-- Contract for reading one encoded instance at any address. The spare
address cell covers the table scanner's end-pointer arithmetic. -/
def demandCheckContract (w : ℕ) (I : Instance) : Contract where
  pre args mem := ∃ a U, args = [a, U] ∧ ListAt mem a I.encode ∧
    a + I.encode.length + 1 < 2 ^ w ∧ I.m * U < 2 ^ w ∧
      ∀ x ∈ I.encode, x < 2 ^ w
  post args mem v mem' := mem' = mem ∧
    v = if FlowReduction.demandBoundCheck I (args.getD 1 0) then 1 else 0
  cost _ _ := 24 * I.n + 100

/-- Neither procedure contains a random instruction. -/
theorem demandCheckModule_noRand (b : ℕ) : ∀ s ∈ demandCheckModule b, s.NoRand := by
  simp only [demandCheckModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨by simp only [demandCheckBody, Stmt.NoRand, and_self],
    tableBoundBody_noRand _⟩

/-- The demand check computes the model test directly from the required input
encoding, in linear time in the number of vertices on every random tape. -/
theorem demandCheck_meetsContract {w b : ℕ} {p : Program} (hw : 8 < 2 ^ w)
    (hp : p.HasAt b (demandCheckModule b)) (I : Instance) (hv : I.IsValid) :
    MeetsContract w p b (demandCheckContract w I) := by
  have hscan : p.HasAt (b + 1) (tableBoundModule (b + 1)) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [tableBoundModule, demandCheckModule, Nat.add_zero, List.getElem_cons_succ,
      List.getElem_cons_zero] using hp 1 (by simp only [demandCheckModule, List.length_cons, List.length_nil]; omega)
  have hk := tableBound_meetsContract (by omega : 1 < 2 ^ w) hscan
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, U, rfl, hat, hend, hproduct, hinput⟩ := hpre
  have ha : a < 2 ^ w := hwords a (by simp)
  have hU : U < 2 ^ w := hwords U (by simp)
  have hheader := instance_header_at I mem a hat
  have hN := hheader.1
  have hM := hheader.2
  have hn : I.n < 2 ^ w := hinput I.n (List.mem_cons_self)
  have hm : I.m < 2 ^ w := hinput I.m (List.mem_cons_of_mem _ (List.mem_cons_self))
  have hlength := instance_encode_length I hv
  have haddr : a + 3 + 8 * I.m < 2 ^ w := by omega
  have haddr1 : a + 1 < 2 ^ w := by omega
  have h8m : 8 * I.m < 2 ^ w := by omega
  have hplus3 : a + 3 < 2 ^ w := by omega
  have hscanend : a + 3 + 8 * I.m + 2 * I.n < 2 ^ w := by omega
  have hvals : ∀ i < I.n, mem (a + 3 + 8 * I.m + 2 * i) < 2 ^ w := by
    intro i hi
    have hget := demand_magnitude_at I hv mem a hat ⟨i, hi⟩
    have hidx : 2 + 8 * I.m + 2 * i + 1 < I.encode.length := by omega
    have hx : I.encode.getD (2 + 8 * I.m + 2 * i + 1) 0 ∈ I.encode := by
      rw [List.getD_eq_getElem _ _ hidx]
      exact List.getElem_mem hidx
    have hh := hinput _ hx
    rw [instance_encode_demand_magnitude I hv ⟨i, hi⟩] at hh
    have he : a + 3 + 8 * I.m + 2 * i = a + (2 + 8 * I.m + 2 * i + 1) := by omega
    rw [he, hget]
    exact hh
  apply runs_start_le
  unfold demandCheckBody
  refine runs_seq_assign_le (v := I.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := I.m) (by eval_expr) ?_
  refine runs_seq_call_le hk (by eval_expr) ?_ ?_ ?_
  · wram_words
  · change ∃ a' length stride bound,
      [a + 3 + 8 * I.m, I.n, 2, I.m * U] = [a', length, stride, bound] ∧
        a' + stride * length < 2 ^ w ∧ ∀ i < length, mem (a' + stride * i) < 2 ^ w
    exact ⟨_, _, _, _, rfl, hscanend, hvals⟩
  · intro v mem' pos' hpost
    obtain ⟨hmem, hout⟩ := hpost
    subst mem'
    change v = if tableBoundCheck mem (a + 3 + 8 * I.m) 2 I.n (I.m * U) then 1 else 0 at hout
    have hvword : v < 2 ^ w := by split at hout <;> omega
    refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
    · change mem = mem ∧ v = if FlowReduction.demandBoundCheck I U then 1 else 0
      exact ⟨rfl, (tableBoundCheck_demand I hv U mem a hat) ▸ hout⟩
    · simp only [demandCheckContract, tableBoundContract, List.getD_cons_zero, List.getD_cons_succ,
        Expr.size_bin, Expr.size_const, Expr.size_reg, Expr.size_load, argsSize_cons, argsSize_nil]
      omega

end MinCostFlow.Scaling.Machine
